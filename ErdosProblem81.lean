import Mathlib

/-
We prove that every chordal graph `G` on `n ≥ 3` vertices satisfies
`cp G ≤ (1/4 - c₀) n²`, where `cp G` is the clique partition
number and `c₀ ≥ 1/133`.

This is an explicit version of a theorem of Erdős, Ordman and Zalcstein, which
they proved in their 1993 paper.

Erdős, Paul and Ordman, Edward T. and Zalcstein, Yechezkel, Clique partitions of
chordal graphs. Combin. Probab. Comput. (1993), 409-415.

Proving that one can take `c₀ = 1/12 + o(1)` is Erdős Problem #81
(https://www.erdosproblems.com/81).

The formalization below was obtained by Aristotle from Harmonic
(aristotle-harmonic@harmonic.fun), and was based on a optimized blueprint
that was written by ChatGPT 5.5 Pro.

Lean version: leanprover/lean4:v4.28.0
-/

open SimpleGraph Real
open scoped Classical

set_option maxHeartbeats 2000000

noncomputable section

namespace Erdos81

variable {V : Type*} [Fintype V]

/-
A couple of basic definitions.
-/
/-- `eIn G X` is the number of edges of `G` with both endpoints in `X`,
i.e. `|E(G[X])|`. -/
def eIn (G : SimpleGraph V) (X : Finset V) : ℕ :=
  ((X.powersetCard 2).filter (fun s => G.IsClique (s : Set V))).card

/-- `eBetween G X Y` is the number of edges with one endpoint in `X` and one in
`Y` (intended for disjoint `X`, `Y`). -/
def eBetween (G : SimpleGraph V) (X Y : Finset V) : ℕ :=
  ((X ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card

/-- A family `P` of subsets is a clique partition of `G` if every member is a
clique of order at least two, and every edge lies in the binomial set of exactly
one member. -/
def IsCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ Q ∈ P, G.IsClique (Q : Set V) ∧ 2 ≤ Q.card) ∧
  (∀ x y, G.Adj x y → ∃! Q : Finset V, Q ∈ P ∧ x ∈ Q ∧ y ∈ Q)

/-- The clique partition number `cp G` is the least size of a clique
partition of `G`.  It is `0` when `G` has no edges. -/
def cp (G : SimpleGraph V) : ℕ :=
  sInf { n | ∃ P : Finset (Finset V), IsCliquePartition G P ∧ P.card = n }

/-- A family `P` of subsets is a clique partition of the edges inside `C`:
every member is a clique of order at least two contained in `C`, and every edge
with both endpoints in `C` lies in exactly one member. -/
def IsCliquePartitionOn (G : SimpleGraph V) (C : Finset V) (P : Finset (Finset V)) : Prop :=
  (∀ Q ∈ P, Q ⊆ C ∧ G.IsClique (Q : Set V) ∧ 2 ≤ Q.card) ∧
  (∀ x y, x ∈ C → y ∈ C → G.Adj x y → ∃! Q : Finset V, Q ∈ P ∧ x ∈ Q ∧ y ∈ Q)

/-- A graph is chordal if every cycle of length at least four has a chord:
an edge between two of its vertices that is not one of the cycle edges.  This is
equivalent to having no induced cycle of order at least four. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ {v : V} (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-- `A` is a maximum clique of `G` if it is a clique of largest order. -/
def IsMaxClique (G : SimpleGraph V) (A : Finset V) : Prop :=
  G.IsClique (A : Set V) ∧ ∀ B : Finset V, G.IsClique (B : Set V) → B.card ≤ A.card

/-- The neighbours of `v` lying in `C`. -/
def cnbhd (G : SimpleGraph V) (C : Finset V) (v : V) : Finset V :=
  C.filter (fun u => G.Adj v u)

/-- `v` is simplicial relative to `C` if its `C`-neighbourhood is a clique. -/
def IsSimplicialOn (G : SimpleGraph V) (C : Finset V) (v : V) : Prop :=
  G.IsClique ((cnbhd G C v : Finset V) : Set V)

/-- `ReachIn G A x y`: there is a walk from `x` to `y` all of whose vertices lie
in `A`. -/
def ReachIn (G : SimpleGraph V) (A : Finset V) (x y : V) : Prop :=
  ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ A

/-- A walk is induced if every adjacency between two of its vertices is one
of its own edges (no chords). -/
def InducedWalk (G : SimpleGraph V) {x y : V} (w : G.Walk x y) : Prop :=
  ∀ a ∈ w.support, ∀ b ∈ w.support, G.Adj a b → s(a, b) ∈ w.edges

/-
Some basic facts about `ReachIn`.
-/
omit [Fintype V] in
lemma reachIn_mem_right (G : SimpleGraph V) (A : Finset V) {x y : V}
    (h : ReachIn G A x y) : y ∈ A := by
  obtain ⟨w, hw⟩ := h; exact hw y (by simp)

omit [Fintype V] in
lemma reachIn_refl (G : SimpleGraph V) (A : Finset V) {x : V} (hx : x ∈ A) :
    ReachIn G A x x :=
  ⟨Walk.nil, by simp [hx]⟩

omit [Fintype V] in
lemma reachIn_symm (G : SimpleGraph V) (A : Finset V) {x y : V}
    (h : ReachIn G A x y) : ReachIn G A y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, by intro z hz; exact hw z (by simpa using hz)⟩

omit [Fintype V] in
lemma reachIn_trans (G : SimpleGraph V) (A : Finset V) {x y z : V}
    (h1 : ReachIn G A x y) (h2 : ReachIn G A y z) : ReachIn G A x z := by
  obtain ⟨w1, hw1⟩ := h1; obtain ⟨w2, hw2⟩ := h2
  refine ⟨w1.append w2, ?_⟩
  intro t ht
  rw [Walk.support_append] at ht
  rcases List.mem_append.1 ht with h | h
  · exact hw1 t h
  · exact hw2 t (List.mem_of_mem_tail h)

omit [Fintype V] in
lemma reachIn_of_adj (G : SimpleGraph V) (A : Finset V) {x y : V}
    (hxy : G.Adj x y) (hx : x ∈ A) (hy : y ∈ A) : ReachIn G A x y :=
  ⟨Walk.cons hxy Walk.nil, by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption⟩

omit [Fintype V] in
lemma reachIn_adj_right (G : SimpleGraph V) (A : Finset V) {x y z : V}
    (h : ReachIn G A x y) (hyz : G.Adj y z) (hz : z ∈ A) : ReachIn G A x z :=
  reachIn_trans G A h (reachIn_of_adj G A hyz (reachIn_mem_right G A h) hz)

omit [Fintype V] in
/-- All vertices of a walk that stays in `A` and starts at `x` are reachable from
`x` inside `A` (hence in `x`'s component). -/
lemma reachIn_of_walk_support (G : SimpleGraph V) (A : Finset V) {x y : V}
    (w : G.Walk x y) (hw : ∀ z ∈ w.support, z ∈ A) {a : V} (ha : a ∈ w.support) :
    ReachIn G A x a :=
  ⟨w.takeUntil a ha, fun z hz => hw z (w.support_takeUntil_subset ha hz)⟩

/-
Helper lemmas on appended/reversed walks.
-/
omit [Fintype V] in
lemma mem_support_append_reverse (G : SimpleGraph V) {u v : V} (p q : G.Walk u v) {z : V} :
    z ∈ (p.append q.reverse).support ↔ z ∈ p.support ∨ z ∈ q.support := by
  rw [Walk.mem_support_append_iff]
  simp [Walk.support_reverse]

omit [Fintype V] in
lemma mem_edges_append_reverse (G : SimpleGraph V) {u v : V} (p q : G.Walk u v) {e : Sym2 V} :
    e ∈ (p.append q.reverse).edges ↔ e ∈ p.edges ∨ e ∈ q.edges := by
  rw [Walk.edges_append]
  simp [Walk.edges_reverse]

/-
If `p` and `q` are paths from `u` to `v` (with `u ≠ v` nonadjacent, each of
length ≥ 2) sharing only the endpoints `u` and `v`, then `p.append q.reverse` is
a cycle.
-/
omit [Fintype V] in
lemma append_reverse_isCycle (G : SimpleGraph V) {u v : V} (hne : u ≠ v)
    (hnadj : ¬ G.Adj u v) (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hcap : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v) :
    (p.append q.reverse).IsCycle := by
  simp +decide [ SimpleGraph.Walk.isCycle_def ];
  refine' ⟨ _, _, _ ⟩;
  · simp_all +decide [ SimpleGraph.Walk.isTrail_def ];
    have h_disjoint : Disjoint (p.edges.toFinset) (q.edges.toFinset) := by
      rw [ Finset.disjoint_left ];
      intro e heq heq';
      rcases e with ⟨ x, y ⟩;
      have hxy : x ∈ p.support ∧ y ∈ p.support ∧ x ∈ q.support ∧ y ∈ q.support := by
        have hxy : ∀ {u v : V} {w : G.Walk u v}, ∀ e ∈ w.edges, ∀ x y, e = s(x, y) → x ∈ w.support ∧ y ∈ w.support := by
          intros u v w e he x y heq; induction w <;> aesop;
        exact ⟨ hxy _ ( by simpa using heq ) _ _ rfl |>.1, hxy _ ( by simpa using heq ) _ _ rfl |>.2, hxy _ ( by simpa using heq' ) _ _ rfl |>.1, hxy _ ( by simpa using heq' ) _ _ rfl |>.2 ⟩;
      cases hcap x hxy.1 hxy.2.2.1 <;> cases hcap y hxy.2.1 hxy.2.2.2 <;> simp_all +decide;
      · exact absurd heq ( by simpa using p.edges_subset_edgeSet heq );
      · exact hnadj ( by simpa using p.adj_of_mem_edges heq );
      · exact hnadj ( by simpa [ SimpleGraph.adj_comm ] using p.adj_of_mem_edges heq );
      · exact absurd heq ( by simpa using p.edges_subset_edgeSet heq );
    simp_all +decide [ Finset.disjoint_left, List.nodup_append ];
    exact ⟨ hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, fun a ha b hb hab => h_disjoint ha <| hab ▸ hb ⟩;
  · cases p <;> cases q <;> aesop;
  · have h_tail_nodup : p.support.tail.Nodup ∧ (q.reverse.support.tail).Nodup ∧ Disjoint (p.support.tail.toFinset) (q.reverse.support.tail.toFinset) := by
      refine' ⟨ _, _, _ ⟩;
      · exact hp.support_nodup.tail;
      · simp_all +decide [ SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_reverse ];
        exact hq.sublist ( List.dropLast_sublist _ );
      · simp_all +decide [ Finset.disjoint_left ];
        intro z hz₁ hz₂; specialize hcap z; simp_all +decide [ List.mem_iff_get ] ;
        rcases hz₁ with ⟨ n, rfl ⟩ ; rcases hz₂ with ⟨ m, hm ⟩ ; specialize hcap ⟨ n + 1, by
          lia ⟩ rfl ⟨ m, by
          exact lt_of_lt_of_le m.2 ( by simp ) ⟩ hm ; simp_all +decide [ SimpleGraph.Walk.isPath_def ];
        cases hcap <;> simp_all +decide ;
        · rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide;
          grind;
        · have := List.nodup_iff_injective_get.mp hq; have := @this ⟨ m, by
            exact lt_of_lt_of_le m.2 ( by simp ) ⟩ ⟨ q.support.length - 1, by
            exact Nat.pred_lt ( ne_bot_of_gt ( List.length_pos_iff.mpr ( by aesop ) ) ) ⟩ ; simp_all +decide ;
          generalize_proofs at *;
          grind;
    rw [ SimpleGraph.Walk.support_append ] ; simp_all +decide [ List.nodup_append ] ;
    exact fun a ha b hb hab => h_tail_nodup.2.2 ha ( hab ▸ hb )

/-
If a path `p` from `u` to `v` has two vertices `a`, `b` in its support that are
adjacent in `G` but whose edge is not on `p` (a chord), then there is a strictly
shorter `u`-`v` walk whose support is contained in that of `p`.
-/
omit [Fintype V] in
lemma exists_shortcut (G : SimpleGraph V) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    {a b : V} (ha : a ∈ p.support) (hb : b ∈ p.support) (hab : G.Adj a b)
    (hnotedge : s(a, b) ∉ p.edges) :
    ∃ w : G.Walk u v, (∀ z ∈ w.support, z ∈ p.support) ∧ w.length < p.length := by
  by_contra! h_contra;
  obtain ⟨q₁, q₂, hq₁, hq₂⟩ : ∃ q₁ : G.Walk u a, ∃ q₂ : G.Walk a v, p = q₁.append q₂ ∧ q₁.IsPath ∧ q₂.IsPath := by
    exact ⟨ p.takeUntil a ha, p.dropUntil a ha, by rw [ SimpleGraph.Walk.take_spec ], hp.takeUntil _, hp.dropUntil _ ⟩;
  by_cases hbq₂ : b ∈ q₂.support;
  · obtain ⟨q₃, q₄, hq₃, hq₄⟩ : ∃ q₃ : G.Walk a b, ∃ q₄ : G.Walk b v, q₂ = q₃.append q₄ ∧ q₃.IsPath ∧ q₄.IsPath := by
      exact ⟨ q₂.takeUntil b hbq₂, q₂.dropUntil b hbq₂, by rw [ SimpleGraph.Walk.take_spec ], by exact hq₂.2.takeUntil _, by exact hq₂.2.dropUntil _ ⟩;
    specialize h_contra ( q₁.append ( SimpleGraph.Walk.cons hab q₄ ) ) ; simp_all +decide [ SimpleGraph.Walk.edges_append ];
    rcases q₃ with ( _ | ⟨ _, _, q₃ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.length ];
    linarith [ h_contra fun z hz => by aesop ];
  · obtain ⟨q₃, q₄, hq₃, hq₄⟩ : ∃ q₃ : G.Walk u b, ∃ q₄ : G.Walk b a, q₁ = q₃.append q₄ ∧ q₃.IsPath ∧ q₄.IsPath := by
      have hbq₁ : b ∈ q₁.support := by
        simp_all +decide [ SimpleGraph.Walk.support_append ];
        exact hb.resolve_right fun h => hbq₂ <| List.mem_of_mem_tail h;
      exact ⟨ q₁.takeUntil b hbq₁, q₁.dropUntil b hbq₁, by rw [ SimpleGraph.Walk.take_spec ], by exact hq₂.1.takeUntil _, by exact hq₂.1.dropUntil _ ⟩;
    specialize h_contra ( q₃.append ( SimpleGraph.Walk.cons hab.symm q₂ ) ) ; simp_all +decide [ SimpleGraph.Walk.length_append ];
    rcases q₄ with ( _ | ⟨ _, _, q₄ ⟩ ) <;> simp_all +decide [ add_assoc ];
    grind

omit [Fintype V] in
/-- If there is a walk from `u` to `v` staying inside `insert u (insert v A)`,
  and `u, v` are distinct and nonadjacent, then there is an *induced* path from
  `u` to `v` of length at least two whose internal vertices all lie in `A`
  (equivalently, whose support is contained in `insert u (insert v A)`). -/
lemma exists_induced_path (G : SimpleGraph V) (A : Finset V) (u v : V)
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (w0 : G.Walk u v) (hw0 : ∀ z ∈ w0.support, z ∈ insert u (insert v A)) :
    ∃ p : G.Walk u v, p.IsPath ∧ (∀ z ∈ p.support, z ∈ insert u (insert v A)) ∧
      InducedWalk G p ∧ 2 ≤ p.length := by
  classical
  have hne0 : ∃ n, ∃ p : G.Walk u v,
      (∀ z ∈ p.support, z ∈ insert u (insert v A)) ∧ p.length = n :=
    ⟨w0.length, w0, hw0, rfl⟩
  obtain ⟨p, hpS, hpe⟩ := Nat.find_spec hne0
  set m := Nat.find hne0 with hm
  have hmin : ∀ q : G.Walk u v,
      (∀ z ∈ q.support, z ∈ insert u (insert v A)) → m ≤ q.length :=
    fun q hq => Nat.find_min' hne0 ⟨q, hq, rfl⟩
  have hbsub : ∀ z ∈ p.bypass.support, z ∈ insert u (insert v A) :=
    fun z hz => hpS z (p.support_bypass_subset hz)
  have hblen : p.bypass.length = m :=
    le_antisymm (hpe ▸ p.length_bypass_le) (hmin _ hbsub)
  refine ⟨p.bypass, p.bypass_isPath, hbsub, ?_, ?_⟩
  · intro a ha b hb hab
    by_contra hcon
    obtain ⟨w, hwsub, hwlen⟩ :=
      exists_shortcut G p.bypass p.bypass_isPath ha hb hab hcon
    have hwm : m ≤ w.length := hmin w (fun z hz => hbsub _ (hwsub z hz))
    omega
  · by_contra hlt
    push_neg at hlt
    interval_cases h : p.bypass.length
    · exact hne (Walk.eq_of_length_eq_zero h)
    · exact hnadj (Walk.adj_of_length_eq_one h)

omit [Fintype V] in
/-- In a chordal graph, there cannot be two induced `u`-`v` paths (each of
  length ≥ 2) whose internal vertices lie in disjoint sets `A` and `B`, when `u
  ≠ v` are nonadjacent.  Their union would be a chordless cycle of length ≥ 4.
  -/
lemma no_two_paths (G : SimpleGraph V) (hG : IsChordal G) (A B : Finset V)
    (hAB : Disjoint A B) (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (u v : V) (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (p : G.Walk u v) (hp : p.IsPath)
    (hpA : ∀ z ∈ p.support, z ∈ insert u (insert v A)) (hpind : InducedWalk G p)
    (hp2 : 2 ≤ p.length)
    (q : G.Walk u v) (hq : q.IsPath)
    (hqB : ∀ z ∈ q.support, z ∈ insert u (insert v B)) (hqind : InducedWalk G q)
    (hq2 : 2 ≤ q.length) : False := by
  simp only [Finset.mem_insert] at hpA hqB
  have huvp : u ∈ p.support ∧ v ∈ p.support := ⟨p.start_mem_support, p.end_mem_support⟩
  have huvq : u ∈ q.support ∧ v ∈ q.support := ⟨q.start_mem_support, q.end_mem_support⟩
  have hcap : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v := by
    intro z hzp hzq
    rcases hpA z hzp with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rcases hqB z hzq with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact (Finset.disjoint_left.mp hAB h h').elim
  have hcyc := append_reverse_isCycle G hne hnadj p q hp hq hp2 hq2 hcap
  have hlen : 4 ≤ (p.append q.reverse).length := by
    rw [Walk.length_append, Walk.length_reverse]; omega
  obtain ⟨x, y, hx, hy, hxy, hxye⟩ := hG _ hcyc hlen
  rw [mem_support_append_reverse] at hx hy
  apply hxye
  rw [mem_edges_append_reverse]
  have same : (x ∈ p.support ∧ y ∈ p.support) ∨ (x ∈ q.support ∧ y ∈ q.support) := by
    rcases hx with hxp | hxq
    · rcases hy with hyp | hyq
      · exact Or.inl ⟨hxp, hyp⟩
      · by_cases hyp : y ∈ p.support
        · exact Or.inl ⟨hxp, hyp⟩
        · have hyB : y ∈ B := by
            rcases hqB y hyq with h | h | h
            · exact absurd (by rw [h]; exact huvp.1) hyp
            · exact absurd (by rw [h]; exact huvp.2) hyp
            · exact h
          rcases hpA x hxp with h | h | h
          · exact Or.inr ⟨by rw [h]; exact huvq.1, hyq⟩
          · exact Or.inr ⟨by rw [h]; exact huvq.2, hyq⟩
          · exact absurd hxy (hsep x h y hyB)
    · rcases hy with hyp | hyq
      · by_cases hxp : x ∈ p.support
        · exact Or.inl ⟨hxp, hyp⟩
        · have hxB : x ∈ B := by
            rcases hqB x hxq with h | h | h
            · exact absurd (by rw [h]; exact huvp.1) hxp
            · exact absurd (by rw [h]; exact huvp.2) hxp
            · exact h
          rcases hpA y hyp with h | h | h
          · exact Or.inr ⟨hxq, by rw [h]; exact huvq.1⟩
          · exact Or.inr ⟨hxq, by rw [h]; exact huvq.2⟩
          · exact absurd hxy.symm (hsep y h x hxB)
      · exact Or.inr ⟨hxq, hyq⟩
  rcases same with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (hpind x h1 y h2 hxy)
  · exact Or.inr (hqind x h1 y h2 hxy)

/-- The component of `x` inside the alive set `A`. -/
def compOf (G : SimpleGraph V) (A : Finset V) (x : V) : Finset V :=
  A.filter (fun z => ReachIn G A x z)

omit [Fintype V] in
lemma mem_compOf (G : SimpleGraph V) (A : Finset V) (x z : V) :
    z ∈ compOf G A x ↔ z ∈ A ∧ ReachIn G A x z := by
  simp [compOf]

omit [Fintype V] in
/-- A walk between two vertices of the same component of `A` can be taken to stay
inside that component. -/
lemma reachIn_walk_in_component (G : SimpleGraph V) (A : Finset V) (x a a' : V)
    (ha : ReachIn G A x a) (ha' : ReachIn G A x a') :
    ∃ w : G.Walk a a', ∀ z ∈ w.support, z ∈ compOf G A x := by
  obtain ⟨w, hw⟩ := reachIn_trans G A (reachIn_symm G A ha) ha'
  refine ⟨w, fun z hz => ?_⟩
  rw [mem_compOf]
  refine ⟨hw z hz, reachIn_trans G A ha (reachIn_of_walk_support G A w hw hz)⟩

omit [Fintype V] in
/-- Build a walk from `s` to `t` through the component of `x`, given that `s` and
`t` each have a neighbour in that component. -/
lemma build_st_walk (G : SimpleGraph V) (A : Finset V) (x s t a a' : V)
    (hsa : G.Adj s a) (hta' : G.Adj t a')
    (ha : ReachIn G A x a) (ha' : ReachIn G A x a') :
    ∃ w : G.Walk s t, ∀ z ∈ w.support, z ∈ insert s (insert t (compOf G A x)) := by
  obtain ⟨w, hw⟩ := reachIn_walk_in_component G A x a a' ha ha'
  refine ⟨Walk.cons hsa (w.append (Walk.cons hta'.symm Walk.nil)), fun z hz => ?_⟩
  simp only [Walk.support_cons, Walk.support_append, Walk.support_nil, List.mem_cons,
    List.mem_append, List.tail_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | hz | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hw z hz))
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

omit [Fintype V] in
/-- If `x` and `y` are in different components of the alive set `A`, and `s`,
  `t` are two distinct vertices outside `A` each having a neighbour in the
  component of `x` and a neighbour in the component of `y`, then in a chordal
  graph `s` and `t` must be adjacent. -/
lemma minsep_pair_adj (G : SimpleGraph V) (hG : IsChordal G) (A : Finset V) (x y : V)
    (hxy : ¬ ReachIn G A x y)
    (s t : V) (hst : s ≠ t)
    (hsx : ∃ a, G.Adj s a ∧ ReachIn G A x a) (hsy : ∃ b, G.Adj s b ∧ ReachIn G A y b)
    (htx : ∃ a, G.Adj t a ∧ ReachIn G A x a) (hty : ∃ b, G.Adj t b ∧ ReachIn G A y b) :
    G.Adj s t := by
  by_contra hnadj
  obtain ⟨a, hsa, hxa⟩ := hsx
  obtain ⟨a', hta', hxa'⟩ := htx
  obtain ⟨b, hsb, hyb⟩ := hsy
  obtain ⟨b', htb', hyb'⟩ := hty
  obtain ⟨w1, hw1⟩ := build_st_walk G A x s t a a' hsa hta' hxa hxa'
  obtain ⟨w2, hw2⟩ := build_st_walk G A y s t b b' hsb htb' hyb hyb'
  obtain ⟨p, hp, hpS, hpind, hp2⟩ :=
    exists_induced_path G (compOf G A x) s t hst hnadj w1 hw1
  obtain ⟨q, hq, hqS, hqind, hq2⟩ :=
    exists_induced_path G (compOf G A y) s t hst hnadj w2 hw2
  have hdisj : Disjoint (compOf G A x) (compOf G A y) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    rw [mem_compOf] at hzx hzy
    exact hxy (reachIn_trans G A hzx.2 (reachIn_symm G A hzy.2)) |>.elim
  have hsep : ∀ c ∈ compOf G A x, ∀ d ∈ compOf G A y, ¬ G.Adj c d := by
    intro c hc d hd hcd
    rw [mem_compOf] at hc hd
    exact hxy (reachIn_trans G A (reachIn_adj_right G A hc.2 hcd hd.1) (reachIn_symm G A hd.2))
  exact no_two_paths G hG (compOf G A x) (compOf G A y) hdisj hsep s t hst hnadj
    p hp hpS hpind hp2 q hq hqS hqind hq2

/-
Simpliciality helpers.
-/
omit [Fintype V] in
lemma mem_cnbhd (G : SimpleGraph V) (W : Finset V) (v u : V) :
    u ∈ cnbhd G W v ↔ u ∈ W ∧ G.Adj v u := by
  simp [cnbhd]

omit [Fintype V] in
/-- In a complete (relative) graph every vertex is simplicial. -/
lemma simplicial_of_complete (G : SimpleGraph V) (W : Finset V)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → G.Adj a b) (v : V) :
    IsSimplicialOn G W v := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_cnbhd] at ha hb
  exact hW a ha.1 b hb.1 hab

omit [Fintype V] in
/-- The `W`-neighbourhood of `v` equals its `W'`-neighbourhood when all
`W`-neighbours already lie in `W'`. -/
lemma cnbhd_eq_of_subset (G : SimpleGraph V) {W W' : Finset V} (hWW' : W' ⊆ W)
    {v : V} (h : cnbhd G W v ⊆ W') : cnbhd G W v = cnbhd G W' v := by
  apply Finset.Subset.antisymm
  · intro u hu
    rw [mem_cnbhd] at hu ⊢
    exact ⟨h (by rw [mem_cnbhd]; exact hu), hu.2⟩
  · intro u hu
    rw [mem_cnbhd] at hu ⊢
    exact ⟨hWW' hu.1, hu.2⟩

omit [Fintype V] in
/-- Simpliciality is inherited from a subset containing the whole
neighbourhood. -/
lemma simplicial_inheritance (G : SimpleGraph V) {W W' : Finset V} (hWW' : W' ⊆ W)
    {v : V} (hcl : cnbhd G W v ⊆ W') (h : IsSimplicialOn G W' v) :
    IsSimplicialOn G W v := by
  unfold IsSimplicialOn at h ⊢
  rwa [cnbhd_eq_of_subset G hWW' hcl]

omit [Fintype V] in
/-- Neighbours of a vertex of a component stay in that component. -/
lemma cnbhd_subset_compOf (G : SimpleGraph V) (W : Finset V) (x v : V)
    (hv : v ∈ compOf G W x) : cnbhd G W v ⊆ compOf G W x := by
  intro u hu
  rw [mem_cnbhd] at hu
  rw [mem_compOf] at hv ⊢
  exact ⟨hu.1, reachIn_adj_right G W hv.2 hu.2 hu.1⟩

omit [Fintype V] in
/-- Neighbours of a vertex `v` of the component of `x` in `W \ S` stay in that
component together with `S`. -/
lemma cnbhd_subset_comp_sep (G : SimpleGraph V) (W S : Finset V) (x v : V)
    (hv : v ∈ compOf G (W \ S) x) : cnbhd G W v ⊆ compOf G (W \ S) x ∪ S := by
  intro u hu
  rw [mem_cnbhd] at hu
  by_cases huS : u ∈ S
  · exact Finset.mem_union_right _ huS
  · refine Finset.mem_union_left _ ?_
    rw [mem_compOf] at hv ⊢
    have huA : u ∈ W \ S := Finset.mem_sdiff.mpr ⟨hu.1, huS⟩
    exact ⟨huA, reachIn_adj_right G (W \ S) hv.2 hu.2 huA⟩

/-
If `x ≠ y` are nonadjacent vertices of `W`, there is a separator `S ⊆ W`
(deleting which disconnects `x` from `y` inside `W`) that is inclusion-minimal:
adding back any single vertex of `S` reconnects `x` and `y`.
-/
omit [Fintype V] in
lemma exists_min_separator (G : SimpleGraph V) (W : Finset V) (x y : V)
    (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y ∧
      ∀ s ∈ S, ReachIn G (insert s (W \ S)) x y := by
  -- By the well-ordering principle, there exists a minimal set $S$ that separates $x$ and $y$ in $W$.
  obtain ⟨S, hS⟩ : ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y ∧ ∀ T ⊆ W, x ∉ T ∧ y ∉ T ∧ ¬ ReachIn G (W \ T) x y → S.card ≤ T.card := by
    obtain ⟨S, hS⟩ : ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y := by
      refine' ⟨ W \ { x, y }, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      rintro ⟨ w, hw ⟩;
      rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
      cases hw.1 <;> simp_all +decide;
    have h_min : ∃ m ∈ {k : ℕ | ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y ∧ k = S.card}, ∀ k ∈ {k : ℕ | ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y ∧ k = S.card}, m ≤ k := by
      exact ⟨ Nat.find ⟨ _, ⟨ S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, rfl ⟩ ⟩, Nat.find_spec ( ⟨ _, ⟨ S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, rfl ⟩ ⟩ : ∃ k, ∃ S ⊆ W, x ∉ S ∧ y ∉ S ∧ ¬ReachIn G ( W \ S ) x y ∧ k = S.card ), fun k hk => Nat.find_min' _ hk ⟩;
    obtain ⟨ m, ⟨ S, hS₁, hS₂, hS₃, hS₄, rfl ⟩, hm ⟩ := h_min; exact ⟨ S, hS₁, hS₂, hS₃, hS₄, fun T hT₁ hT₂ => hm _ ⟨ T, hT₁, hT₂.1, hT₂.2.1, hT₂.2.2, rfl ⟩ ⟩ ;
  refine' ⟨ S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, fun s hs => _ ⟩;
  contrapose! hS;
  intro hS₁ hS₂ hS₃ hS₄; use S.erase s; simp_all +decide [ Finset.subset_iff ] ;
  exact ⟨ by rw [ show W \ S.erase s = insert s ( W \ S ) by ext; by_cases h : ‹_› = s <;> aesop ] ; exact hS, ⟨ s, hs ⟩ ⟩

/-
The penultimate vertex of a path ending at `s`, all of whose other vertices
lie in `A`, is a neighbour of `s` lying in `A` and reachable from the start
inside `A`.
-/
omit [Fintype V] in
lemma walk_last_step (G : SimpleGraph V) (A : Finset V) {c s : V}
    (r : G.Walk c s) (hr : r.IsPath) (hcs : c ≠ s)
    (hsupp : ∀ z ∈ r.support, z ≠ s → z ∈ A) :
    ∃ a, G.Adj s a ∧ ReachIn G A c a := by
  obtain ⟨a, ha⟩ : ∃ a : V, G.Adj s a ∧ a ∈ r.support ∧ a ≠ s := by
    induction' r with u v p ih;
    · contradiction;
    · simp +zetaDelta at *;
      rename_i h₁ h₂ h₃;
      by_cases h : p = ih <;> simp_all +decide;
      · exact ⟨ v, h₁.symm, Or.inl rfl, hcs ⟩;
      · grind;
  exact ⟨ a, ha.1, ⟨ r.takeUntil a ha.2.1, fun z hz => by
    by_cases hz' : z = s;
    · grind +suggestions;
    · exact hsupp z ( by simpa using SimpleGraph.Walk.support_takeUntil_subset _ _ hz ) hz' ⟩ ⟩

/-
If `s ∉ A` and adding `s` to the alive set `A` reconnects `x` and `y` which were
in different components, then `s` has a neighbour in the component of `x` and a
neighbour in the component of `y`.
-/
omit [Fintype V] in
lemma sep_neighbors (G : SimpleGraph V) (A : Finset V) (x y s : V)
    (hx : x ∈ A) (hy : y ∈ A) (hsA : s ∉ A) (hxy : ¬ ReachIn G A x y)
    (hre : ReachIn G (insert s A) x y) :
    (∃ a, G.Adj s a ∧ ReachIn G A x a) ∧ (∃ b, G.Adj s b ∧ ReachIn G A y b) := by
  -- By assumption, there exists a path $p$ from $x$ to $y$ in $insert s A$.
  obtain ⟨p, hp⟩ : ∃ p : G.Walk x y, p.IsPath ∧ (∀ z ∈ p.support, z ∈ insert s A) := by
    obtain ⟨ p, hp ⟩ := hre;
    use p.bypass;
    simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    exact ⟨ p.bypass_isPath.support_nodup, fun z hz => hp z <| p.support_bypass_subset hz ⟩;
  -- Since $s \notin A$, $s$ must be in the support of $p$.
  have hs_in_p : s ∈ p.support := by
    grind +suggestions;
  refine' ⟨ _, _ ⟩;
  · have := walk_last_step G A ( p.takeUntil s hs_in_p ) ( hp.1.takeUntil hs_in_p ) ?_ ?_;
    · exact this;
    · grind;
    · intro z hz hzs; have := hp.2 z; simp_all +decide [ Finset.mem_insert ] ;
      exact this ( SimpleGraph.Walk.support_takeUntil_subset _ _ hz );
  · obtain ⟨q, hq⟩ : ∃ q : G.Walk y s, q.IsPath ∧ (∀ z ∈ q.support, z ≠ s → z ∈ A) := by
      have := hp.2;
      exact ⟨ p.reverse.takeUntil s ( by aesop ), by
        grind +suggestions, by
        intro z hz hzs; specialize this z; simp_all +decide [ Finset.mem_insert ] ;
        exact this ( by simpa using SimpleGraph.Walk.support_takeUntil_subset _ _ hz ) ⟩;
    have := walk_last_step G A q hq.1 ( show y ≠ s from by rintro rfl; exact hsA hy ) hq.2; aesop;

/-- The bundled statement proved by induction on `|W|`: every nonempty `W` has a
simplicial vertex, and every noncomplete `W` has two nonadjacent simplicial
vertices. -/
def TwoSimpProp (G : SimpleGraph V) (W : Finset V) : Prop :=
  (W.Nonempty → ∃ v ∈ W, IsSimplicialOn G W v) ∧
  ((∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ ¬ G.Adj x y) →
    ∃ s ∈ W, ∃ t ∈ W, s ≠ t ∧ ¬ G.Adj s t ∧ IsSimplicialOn G W s ∧ IsSimplicialOn G W t)

omit [Fintype V] in
/-- A minimal separator is a clique. -/
lemma min_sep_is_clique (G : SimpleGraph V) (hG : IsChordal G) (W : Finset V) (x y : V)
    (S : Finset V) (hxW : x ∈ W) (hyW : y ∈ W) (hxS : x ∉ S) (hyS : y ∉ S)
    (hdis : ¬ ReachIn G (W \ S) x y)
    (hmin : ∀ s ∈ S, ReachIn G (insert s (W \ S)) x y) :
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b := by
  have hxA : x ∈ W \ S := Finset.mem_sdiff.mpr ⟨hxW, hxS⟩
  have hyA : y ∈ W \ S := Finset.mem_sdiff.mpr ⟨hyW, hyS⟩
  intro a ha b hb hab
  have haA : a ∉ W \ S := fun h => (Finset.mem_sdiff.mp h).2 ha
  have hbA : b ∉ W \ S := fun h => (Finset.mem_sdiff.mp h).2 hb
  obtain ⟨⟨a1, ha1, ha1'⟩, ⟨a2, ha2, ha2'⟩⟩ :=
    sep_neighbors G (W \ S) x y a hxA hyA haA hdis (hmin a ha)
  obtain ⟨⟨b1, hb1, hb1'⟩, ⟨b2, hb2, hb2'⟩⟩ :=
    sep_neighbors G (W \ S) x y b hxA hyA hbA hdis (hmin b hb)
  exact minsep_pair_adj G hG (W \ S) x y hdis a b hab
    ⟨a1, ha1, ha1'⟩ ⟨a2, ha2, ha2'⟩ ⟨b1, hb1, hb1'⟩ ⟨b2, hb2, hb2'⟩

/-
Given a clique separator `S` of `W`, the component `C` of `x` in `W \ S`, and
the two-simplicial property for `H = C ∪ S`, there is a vertex of `C` that is
simplicial in `W`.
-/
lemma simplicial_in_side (G : SimpleGraph V) (W S : Finset V) (x : V)
    (hScl : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b)
    (hSW : S ⊆ W) (hxA : x ∈ W \ S)
    (hH : TwoSimpProp G (compOf G (W \ S) x ∪ S)) :
    ∃ v ∈ compOf G (W \ S) x, IsSimplicialOn G W v := by
  by_cases hHc : ∀ a ∈ compOf G ( W \ S ) x ∪ S, ∀ b ∈ compOf G ( W \ S ) x ∪ S, a ≠ b → G.Adj a b;
  · refine' ⟨ x, _, _ ⟩ <;> simp_all +decide [ IsSimplicialOn ];
    · exact mem_compOf _ _ _ _ |>.2 ⟨ Finset.mem_sdiff.2 ⟨ hxA.1, hxA.2 ⟩, reachIn_refl _ _ ( Finset.mem_sdiff.2 ⟨ hxA.1, hxA.2 ⟩ ) ⟩;
    · intro a ha b hb hab; specialize hHc a; simp_all +decide [ cnbhd ] ;
      contrapose! hHc;
      refine' ⟨ _, b, _, hab, hHc ⟩;
      · exact Classical.or_iff_not_imp_right.2 fun h => mem_compOf _ _ _ _ |>.2 ⟨ Finset.mem_sdiff.2 ⟨ ha.1, h ⟩, reachIn_of_adj _ _ ha.2 ( by aesop ) ( by aesop ) ⟩;
      · exact Classical.or_iff_not_imp_right.2 fun h => by rw [ mem_compOf ] ; exact ⟨ by aesop, by exact ⟨ SimpleGraph.Walk.cons hb.2 SimpleGraph.Walk.nil, by aesop ⟩ ⟩ ;
  · obtain ⟨s, t, hs, ht, hst, hsimp⟩ : ∃ s ∈ compOf G (W \ S) x ∪ S, ∃ t ∈ compOf G (W \ S) x ∪ S, s ≠ t ∧ ¬ G.Adj s t ∧ IsSimplicialOn G (compOf G (W \ S) x ∪ S) s ∧ IsSimplicialOn G (compOf G (W \ S) x ∪ S) t := by
      exact hH.2 ( by push_neg at hHc; tauto );
    by_cases hsS : s ∈ S;
    · by_cases htS : hs ∈ S;
      · exact False.elim ( hsimp.1 ( hScl s hsS hs htS hst ) );
      · refine' ⟨ hs, _, _ ⟩;
        · grind;
        · apply simplicial_inheritance G (by
          grind +locals) (by
          apply cnbhd_subset_comp_sep;
          grind) hsimp.2.2;
    · refine' ⟨ s, _, _ ⟩ <;> simp_all +decide [ Finset.mem_union, Finset.mem_sdiff ];
      refine' simplicial_inheritance G _ _ hsimp.2.1;
      · exact Finset.union_subset ( Finset.filter_subset _ _ |> Finset.Subset.trans <| Finset.sdiff_subset ) hSW;
      · exact cnbhd_subset_comp_sep G W S x s t

/-
One simplicial vertex (the `W.Nonempty` half), assuming the induction
hypothesis for all strictly smaller working sets.
-/
lemma one_simp_step (G : SimpleGraph V) (hG : IsChordal G) (W : Finset V)
    (hne : W.Nonempty)
    (IH : ∀ W' : Finset V, W'.card < W.card → TwoSimpProp G W') :
    ∃ v ∈ W, IsSimplicialOn G W v := by
  by_cases hWc : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → G.Adj a b;
  · exact ⟨ hne.choose, hne.choose_spec, simplicial_of_complete G W hWc hne.choose ⟩;
  · obtain ⟨x, hxW, y, hyW, hxy, hnadj⟩ : ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ ¬ G.Adj x y := by
      grind;
    by_cases hr : ReachIn G W x y;
    · obtain ⟨S, hS⟩ : ∃ S : Finset V, S ⊆ W ∧ x ∉ S ∧ y ∉ S ∧ ¬ ReachIn G (W \ S) x y ∧ ∀ s ∈ S, ReachIn G (insert s (W \ S)) x y := by
        apply exists_min_separator G W x y hxW hyW hxy hnadj;
      have hScl : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b := by
        apply min_sep_is_clique G hG W x y S hxW hyW hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2;
      have hH_card : (compOf G (W \ S) x ∪ S).card < W.card := by
        refine' Finset.card_lt_card _;
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        refine' ⟨ _, y, hyW, _, _ ⟩ <;> simp_all +decide [ compOf ];
        grind;
      obtain ⟨ v, hv ⟩ := simplicial_in_side G W S x hScl hS.1 (by
      grind) (IH _ hH_card);
      exact ⟨ v, Finset.mem_filter.mp hv.1 |>.1 |> Finset.mem_sdiff.mp |>.1, hv.2 ⟩;
    · -- Let C := compOf G W x. Then x ∈ C (mem_compOf, reachIn_refl, x ∈ W) so C nonempty, and C ⊆ W.
      set C := compOf G W x
      have hC_nonempty : C.Nonempty := by
        exact ⟨ x, mem_compOf _ _ _ _ |>.2 ⟨ hxW, reachIn_refl _ _ hxW ⟩ ⟩
      have hC_subset : C ⊆ W := by
        exact fun z hz => Finset.mem_filter.mp hz |>.1;
      -- Also y ∉ C (else ReachIn G W x y, contradicting hr), so C ⊂ W and C.card < W.card (Finset.card_lt_card).
      have hC_proper_subset : C ⊂ W := by
        grind +suggestions
      have hC_card_lt_W_card : C.card < W.card := by
        exact Finset.card_lt_card hC_proper_subset;
      obtain ⟨ v, hvC, hv ⟩ := IH C hC_card_lt_W_card |>.1 hC_nonempty;
      exact ⟨ v, hC_subset hvC, simplicial_inheritance G hC_subset ( cnbhd_subset_compOf G W x v hvC ) hv ⟩

/-
Two nonadjacent simplicial vertices (the noncomplete half), assuming the
induction hypothesis for all strictly smaller working sets.
-/
lemma two_simp_step (G : SimpleGraph V) (hG : IsChordal G) (W : Finset V)
    (hpair : ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ ¬ G.Adj x y)
    (IH : ∀ W' : Finset V, W'.card < W.card → TwoSimpProp G W') :
    ∃ s ∈ W, ∃ t ∈ W, s ≠ t ∧ ¬ G.Adj s t ∧ IsSimplicialOn G W s ∧ IsSimplicialOn G W t := by
  by_cases hr : ReachIn G W (hpair.choose) (hpair.choose_spec.2.choose);
  · obtain ⟨S, hS⟩ : ∃ S : Finset V, S ⊆ W ∧ hpair.choose ∉ S ∧ hpair.choose_spec.2.choose ∉ S ∧ ¬ ReachIn G (W \ S) hpair.choose hpair.choose_spec.2.choose ∧ ∀ s ∈ S, ReachIn G (insert s (W \ S)) hpair.choose hpair.choose_spec.2.choose := by
      apply exists_min_separator G W hpair.choose hpair.choose_spec.2.choose hpair.choose_spec.1 hpair.choose_spec.2.choose_spec.1 hpair.choose_spec.2.choose_spec.2.1 hpair.choose_spec.2.choose_spec.2.2;
    -- Apply the induction hypothesis to H1 and H2 to get hH1 and hH2.
    obtain ⟨v1, hv1⟩ : ∃ v1 ∈ compOf G (W \ S) hpair.choose, IsSimplicialOn G W v1 := by
      apply simplicial_in_side G W S hpair.choose (min_sep_is_clique G hG W hpair.choose hpair.choose_spec.2.choose S hpair.choose_spec.1 hpair.choose_spec.2.choose_spec.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2) hS.1 (by
      exact Finset.mem_sdiff.mpr ⟨ hpair.choose_spec.1, hS.2.1 ⟩) (IH (compOf G (W \ S) hpair.choose ∪ S) (by
      refine' Finset.card_lt_card _;
      grind +locals))
    obtain ⟨v2, hv2⟩ : ∃ v2 ∈ compOf G (W \ S) hpair.choose_spec.2.choose, IsSimplicialOn G W v2 := by
      apply simplicial_in_side G W S hpair.choose_spec.2.choose (min_sep_is_clique G hG W hpair.choose hpair.choose_spec.2.choose S hpair.choose_spec.1 hpair.choose_spec.2.choose_spec.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2) hS.1 (by
      exact Finset.mem_sdiff.mpr ⟨ hpair.choose_spec.2.choose_spec.1, hS.2.2.1 ⟩) (IH (compOf G (W \ S) hpair.choose_spec.2.choose ∪ S) (by
      refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr _ ) ) _;
      exact W;
      · refine' ⟨ _, _ ⟩;
        · grind +locals;
        · intro h;
          replace h := Finset.ext_iff.mp h hpair.choose; simp_all +decide [ compOf ] ;
          grind +suggestions;
      · rfl));
    refine' ⟨ v1, _, v2, _, _, _, hv1.2, hv2.2 ⟩;
    · exact Finset.mem_filter.mp hv1.1 |>.1 |> Finset.mem_sdiff.mp |>.1;
    · exact Finset.mem_filter.mp hv2.1 |>.1 |> Finset.mem_sdiff.mp |>.1;
    · intro h;
      have h_contradiction : ReachIn G (W \ S) hpair.choose hpair.choose_spec.2.choose := by
        have h_contradiction : ReachIn G (W \ S) hpair.choose v1 ∧ ReachIn G (W \ S) v2 hpair.choose_spec.2.choose := by
          grind +suggestions;
        grind +suggestions;
      exact hS.2.2.2.1 h_contradiction;
    · intro h;
      have h_contradiction : ReachIn G (W \ S) hpair.choose v2 := by
        grind +suggestions;
      have h_contradiction : ReachIn G (W \ S) hpair.choose hpair.choose_spec.2.choose := by
        apply reachIn_trans;
        exact h_contradiction;
        exact reachIn_symm _ _ ( by simpa using mem_compOf _ _ _ _ |>.1 hv2.1 |>.2 );
      exact hS.2.2.2.1 h_contradiction;
  · obtain ⟨u1, hu1, hu1_simp⟩ : ∃ u1 ∈ compOf G W hpair.choose, IsSimplicialOn G (compOf G W hpair.choose) u1 := by
      apply one_simp_step G hG (compOf G W hpair.choose) (by
      exact ⟨ _, mem_compOf _ _ _ _ |>.2 ⟨ hpair.choose_spec.1, reachIn_refl _ _ hpair.choose_spec.1 ⟩ ⟩) (by
      exact fun W' hW' => IH W' ( lt_of_lt_of_le hW' ( Finset.card_le_card ( Finset.filter_subset _ _ ) ) ))
    obtain ⟨u2, hu2, hu2_simp⟩ : ∃ u2 ∈ compOf G W hpair.choose_spec.2.choose, IsSimplicialOn G (compOf G W hpair.choose_spec.2.choose) u2 := by
      apply one_simp_step G hG (compOf G W hpair.choose_spec.2.choose);
      · exact ⟨ _, mem_compOf _ _ _ _ |>.2 ⟨ hpair.choose_spec.2.choose_spec.1, reachIn_refl _ _ hpair.choose_spec.2.choose_spec.1 ⟩ ⟩;
      · exact fun W' hW' => IH W' ( lt_of_lt_of_le hW' ( Finset.card_le_card ( Finset.filter_subset _ _ ) ) );
    refine' ⟨ u1, _, u2, _, _, _, _ ⟩;
    · exact Finset.mem_filter.mp hu1 |>.1;
    · exact Finset.mem_filter.mp hu2 |>.1;
    · intro h;
      obtain ⟨ w, hw ⟩ := mem_compOf G W _ _ |>.1 hu1;
      grind +suggestions;
    · intro h;
      have h_reach : ReachIn G W hpair.choose u2 := by
        have h_reach : ReachIn G W hpair.choose u1 := by
          exact Finset.mem_filter.mp hu1 |>.2;
        exact reachIn_adj_right G W h_reach h (by
        exact Finset.mem_filter.mp hu2 |>.1);
      grind +suggestions;
    · refine' ⟨ simplicial_inheritance G ( Finset.filter_subset _ _ ) _ hu1_simp, simplicial_inheritance G ( Finset.filter_subset _ _ ) _ hu2_simp ⟩;
      · exact cnbhd_subset_compOf G W hpair.choose u1 ( by simpa using hu1 );
      · intro z hz;
        exact cnbhd_subset_compOf G W _ _ hu2 hz

lemma simplicial_combined (G : SimpleGraph V) (hG : IsChordal G) (W : Finset V) :
    TwoSimpProp G W := by
  induction' hn : W.card using Nat.strong_induction_on with n ih generalizing W
  have IH : ∀ W' : Finset V, W'.card < W.card → TwoSimpProp G W' :=
    fun W' hlt => ih W'.card (hn ▸ hlt) W' rfl
  exact ⟨fun hne => one_simp_step G hG W hne IH, fun hpair => two_simp_step G hG W hpair IH⟩

/-- In a chordal graph, outside any proper clique `D ⊂ C` there is a vertex of
  `C` that is simplicial relative to `C`. -/
lemma exists_simplicial_outside (G : SimpleGraph V) (hG : IsChordal G) (C D : Finset V)
    (hDcl : G.IsClique (D : Set V)) (hproper : D ⊂ C) :
    ∃ v ∈ C, v ∉ D ∧ IsSimplicialOn G C v := by
  obtain ⟨one, two⟩ := simplicial_combined G hG C
  by_cases hcomp : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → G.Adj a b
  · obtain ⟨v, hvC, hvD⟩ : ∃ v, v ∈ C ∧ v ∉ D := by
      obtain ⟨v, hv⟩ := Finset.exists_of_ssubset hproper
      exact ⟨v, hv.1, hv.2⟩
    exact ⟨v, hvC, hvD, simplicial_of_complete G C hcomp v⟩
  · push_neg at hcomp
    obtain ⟨a, haC, b, hbC, hab, hnadj⟩ := hcomp
    obtain ⟨s, hsC, t, htC, hst, hstadj, hssimp, htsimp⟩ :=
      two ⟨a, haC, b, hbC, hab, hnadj⟩
    by_cases hsD : s ∈ D
    · refine ⟨t, htC, ?_, htsimp⟩
      intro htD
      exact hstadj (hDcl (by exact_mod_cast hsD) (by exact_mod_cast htD) hst)
    · exact ⟨s, hsC, hsD, hssimp⟩

/-- `eIn` equals the number of edges with both endpoints in `X`. -/
lemma eIn_card_eq (G : SimpleGraph V) (X : Finset V) :
    eIn G X = (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ X)).card := by
  refine' Eq.symm _;
  refine' Finset.card_bij ( fun e he => Finset.univ.filter fun v => v ∈ e ) _ _ _ <;> simp_all +decide;
  · rintro ⟨ u, v ⟩ huv huX; use ?_, ?_;
    · refine' ⟨ { u, v }, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      rw [ Finset.card_pair huv.ne ];
    · simp_all +decide [SimpleGraph.isClique_iff];
  · rintro b x hx hx' rfl hb; obtain ⟨ a, b, hab, rfl ⟩ := Finset.card_eq_two.1 hx'; use s(a, b); aesop;

/-- For disjoint `X`, `Y`, `eBetween` equals the number of edges with one
endpoint in each. -/
lemma eBetween_card_eq (G : SimpleGraph V) (X Y : Finset V) (hXY : Disjoint X Y) :
    eBetween G X Y =
      (G.edgeFinset.filter (fun e => (∃ v ∈ e, v ∈ X) ∧ (∃ v ∈ e, v ∈ Y))).card := by
  refine' Finset.card_bij ( fun p hp => Sym2.mk p ) _ _ _;
  · aesop;
  · simp +contextual [ Sym2.eq ];
    intro a b ha hb hab a' b' ha' hb' hab' h; cases h <;> simp_all +decide [ Finset.disjoint_left ] ;
  · simp +decide [ Finset.disjoint_left ] at hXY ⊢;
    rintro ⟨ a, b ⟩ hab x hx hx' y hy hy' ; cases hx ; cases hy ; simp_all +decide;
    grind

/-- Decomposition of the edge count by a set and its complement. -/
lemma edges_decomp (G : SimpleGraph V) (A : Finset V) :
    G.edgeFinset.card = eIn G A + eBetween G A Aᶜ + eIn G Aᶜ := by
  rw [ eIn_card_eq, eBetween_card_eq, eIn_card_eq ];
  · rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
    rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
    refine' Finset.card_eq_sum_ones _ ▸ Finset.sum_congr rfl fun x hx => _;
    rcases x with ⟨ u, v ⟩ ; by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp +decide [ hu, hv ];
  · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_compl.mp hx' hx

omit [Fintype V] in
/-- `eBetween` is at most the number of cross pairs. -/
lemma eBetween_le_mul (G : SimpleGraph V) (X Y : Finset V) :
    eBetween G X Y ≤ X.card * Y.card := by
  exact le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide )

/-
Removing `v ∈ C` drops the number of edges inside `C` by the `C`-degree of
`v` (the number of neighbours of `v` inside `C`).
-/
lemma eIn_erase (G : SimpleGraph V) (C : Finset V) (v : V) (hv : v ∈ C) :
    eIn G C = eIn G (C.erase v) + (cnbhd G C v).card := by
  rw [ eIn_card_eq, eIn_card_eq ];
  rw [ ← Finset.card_image_of_injective _ ( show Function.Injective ( fun x : V => Sym2.mk ( v, x ) ) from ?_ ) ];
  · rw [ ← Finset.card_union_of_disjoint ];
    · congr with e ; simp +decide;
      constructor;
      · rcases e with ⟨ x, y ⟩;
        by_cases hx : x = v <;> by_cases hy : y = v <;> simp_all +decide [ cnbhd ];
        · exact fun h1 h2 => ⟨ y, ⟨ h2, h1 ⟩, Or.inl rfl ⟩;
        · exact fun h₁ h₂ => ⟨ x, ⟨ h₂, h₁.symm ⟩, Or.inr rfl ⟩;
      · rintro ( ⟨ he, he' ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ cnbhd ];
    · simp +decide [ Finset.disjoint_right ];
  · intro x y; aesop;

/-
A `C`-simplicial vertex together with its `C`-neighbourhood is a clique
inside `C`, so its `C`-degree is at most `|D| - 1` for a maximum clique `D`.
-/
omit [Fintype V] in
lemma cnbhd_card_lt (G : SimpleGraph V) (C D : Finset V) (v : V) (hv : v ∈ C)
    (hsimp : IsSimplicialOn G C v)
    (hDmax : ∀ B : Finset V, B ⊆ C → G.IsClique (B : Set V) → B.card ≤ D.card) :
    (cnbhd G C v).card + 1 ≤ D.card := by
  contrapose! hDmax;
  refine' ⟨ Insert.insert v ( cnbhd G C v ), _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, IsSimplicialOn ];
  · exact fun x hx => Finset.mem_filter.mp hx |>.1;
  · exact fun x hx hx' => by simpa [ hx' ] using Finset.mem_filter.mp hx |>.2;
  · rw [ Finset.card_insert_of_notMem ] <;> simp_all +decide [ cnbhd ]

/-
In a chordal graph, with `D` a maximum clique of the subset `C` (`k = |D|`), the
edges inside `C` number at most `eIn D + (|C| - k)(k - 1)`.
-/
lemma edges_outside_core (G : SimpleGraph V) (hG : IsChordal G) (C D : Finset V)
    (hDsub : D ⊆ C) (hDcl : G.IsClique (D : Set V))
    (hDmax : ∀ B : Finset V, B ⊆ C → G.IsClique (B : Set V) → B.card ≤ D.card) :
    eIn G C ≤ eIn G D + (C.card - D.card) * (D.card - 1) := by
  revert hDsub hDcl hDmax;
  induction' n : C.card using Nat.strong_induction_on with n ih generalizing C D;
  by_cases hD : D = C;
  · grind;
  · intro hDsub hDcl hDmax
    obtain ⟨v, hvC, hvD, hsimp⟩ : ∃ v ∈ C, v ∉ D ∧ IsSimplicialOn G C v := by
      apply exists_simplicial_outside G hG C D hDcl (Finset.ssubset_iff_subset_ne.mpr ⟨hDsub, hD⟩);
    have h_ind : eIn G (C.erase v) ≤ eIn G D + ((C.card - 1) - D.card) * (D.card - 1) := by
      convert ih ( C.card - 1 ) _ ( C.erase v ) D _ _ _ _ using 1;
      · exact n ▸ Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr ⟨ v, hvC ⟩ ) );
      · exact Finset.card_erase_of_mem hvC;
      · exact fun x hx => Finset.mem_erase_of_ne_of_mem ( by rintro rfl; exact hvD hx ) ( hDsub hx );
      · exact hDcl;
      · exact fun B hB hBcl => hDmax B ( Finset.Subset.trans hB ( Finset.erase_subset _ _ ) ) hBcl;
    have h_card : (cnbhd G C v).card + 1 ≤ D.card := by
      apply cnbhd_card_lt G C D v hvC hsimp hDmax;
    have h_card : eIn G C = eIn G (C.erase v) + (cnbhd G C v).card :=
      eIn_erase G C v hvC
    rw [ ← n ];
    rw [ show C.card - D.card = ( C.card - 1 - D.card ) + 1 by rw [ tsub_right_comm, tsub_add_cancel_of_le ( Nat.succ_le_of_lt ( Nat.sub_pos_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ hDsub, hD ⟩ ) ) ) ) ] ] ; nlinarith [ Nat.sub_add_cancel ( show 1 ≤ D.card from Nat.pos_of_ne_zero ( by aesop_cat ) ) ]

/-
Given a family `𝒬` of cliques of order ≥ 2 whose edges are pairwise disjoint,
`cp G` is at most `|𝒬|` plus the number of edges not covered by any member.
-/
lemma cp_le_cover (G : SimpleGraph V) (𝒬 : Finset (Finset V))
    (hclq : ∀ Q ∈ 𝒬, G.IsClique (Q : Set V) ∧ 2 ≤ Q.card)
    (hdisj : ∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, ∀ x y, G.Adj x y →
       (x ∈ Q₁ ∧ y ∈ Q₁) → (x ∈ Q₂ ∧ y ∈ Q₂) → Q₁ = Q₂) :
    cp G ≤ 𝒬.card +
      (G.edgeFinset.filter (fun e => ¬ ∃ Q ∈ 𝒬, ∀ v ∈ e, v ∈ Q)).card := by
  refine' le_trans ( csInf_le _ _ ) _;
  exact ( 𝒬 ∪ Finset.image ( fun e : Sym2 V => Finset.univ.filter ( · ∈ e ) ) ( Finset.filter ( fun e : Sym2 V => ¬∃ Q ∈ 𝒬, ∀ v ∈ e, v ∈ Q ) G.edgeFinset ) ).card;
  · exact ⟨ 0, fun n hn => hn.choose_spec.2.symm ▸ Nat.zero_le _ ⟩;
  · refine' ⟨ _, ⟨ _, _ ⟩, rfl ⟩;
    · simp +zetaDelta at *;
      rintro Q ( hQ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> simp_all +decide [ SimpleGraph.isClique_iff, Finset.ext_iff ];
      rcases a with ⟨ x, y ⟩ ; simp_all +decide ;
      exact Finset.one_lt_card.2 ⟨ x, by simp +decide, y, by simp +decide [ ha₁.ne ] ⟩;
    · intro x y hxy
      by_cases h : ∃ Q ∈ 𝒬, x ∈ Q ∧ y ∈ Q;
      · obtain ⟨ Q, hQ₁, hQ₂, hQ₃ ⟩ := h;
        refine' ⟨ Q, _, _ ⟩ <;> simp_all +decide ;
        rintro R ( hR₁ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) hx hy <;> simp_all +decide [ Finset.ext_iff ];
        · exact hdisj _ hR₁ _ hQ₁ _ _ hxy hx hy hQ₂ hQ₃;
        · contrapose! ha₂;
          cases a ; aesop;
      · refine' ⟨ { x, y }, _, _ ⟩ <;> simp_all +decide ;
        · refine' Or.inr ⟨ s(x, y), _, _ ⟩ <;> simp_all +decide;
          · exact fun Q hQ => not_and_or.mp fun h' => h Q hQ h'.1 h'.2;
          · aesop;
        · rintro Q ( hQ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) hx hy <;> simp_all +decide [ Finset.ext_iff ];
          rcases a with ⟨ u, v ⟩ ; aesop;
  · exact Finset.card_union_le _ _ |> le_trans <| Nat.add_le_add_left ( Finset.card_image_le ) _

/-- The piecewise count `h(p,q)` of parts in the split-graph partition. -/
def hsplit (p q : ℕ) : ℕ :=
  if q ≤ p then Nat.choose p 2 + p else p * q - Nat.choose p 2

/-
Real value of `hsplit` in the case `q ≤ p`.
-/
lemma hsplit_eq_ge {p q : ℕ} (h : q ≤ p) :
    (hsplit p q : ℝ) = (p : ℝ) ^ 2 / 2 + (p : ℝ) / 2 := by
  unfold hsplit; simp +decide [ *, Nat.choose_two_right ] ; ring_nf;
  cases p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] ; ring

/-
Real value of `hsplit` in the case `p < q`.
-/
lemma hsplit_eq_lt {p q : ℕ} (h : p < q) :
    (hsplit p q : ℝ) = (p : ℝ) * q - (p : ℝ) ^ 2 / 2 + (p : ℝ) / 2 := by
  unfold hsplit;
  rw [ if_neg h.not_ge, Nat.cast_sub ];
  · rw [ Nat.choose_two_right ];
    cases p <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] ; ring;
  · exact le_trans ( Nat.choose_le_pow _ _ ) ( by nlinarith )

/-
Every finite graph has a maximum clique.
-/
lemma exists_maxClique (G : SimpleGraph V) : ∃ A : Finset V, IsMaxClique G A := by
  -- By definition of `IsMaxClique`, we know that every finite graph has a maximum clique.
  have h_max_clique : ∃ A ∈ Finset.filter (fun A : Finset V => G.IsClique (A : Set V)) (Finset.univ : Finset (Finset V)), ∀ B ∈ Finset.filter (fun A : Finset V => G.IsClique (A : Set V)) (Finset.univ : Finset (Finset V)), B.card ≤ A.card := by
    apply_rules [ Finset.exists_max_image ];
    exact ⟨ ∅, by simp +decide ⟩;
  exact ⟨ h_max_clique.choose, h_max_clique.choose_spec.1 |> fun h => by simpa using h, fun B hB => h_max_clique.choose_spec.2 B <| by simpa using hB ⟩

/-
Every nonempty subset contains a maximum clique relative to it (of order ≥ 1).
-/
omit [Fintype V] in
lemma exists_maxClique_on (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) :
    ∃ D : Finset V, D ⊆ C ∧ G.IsClique (D : Set V) ∧
      (∀ B : Finset V, B ⊆ C → G.IsClique (B : Set V) → B.card ≤ D.card) ∧ 1 ≤ D.card := by
  have h_max_clique : ∃ D ∈ Finset.filter (fun B : Finset V => G.IsClique (B : Set V) ∧ B ⊆ C) (Finset.powerset C), ∀ B ∈ Finset.filter (fun B : Finset V => G.IsClique (B : Set V) ∧ B ⊆ C) (Finset.powerset C), B.card ≤ D.card := by
    apply_rules [ Finset.exists_max_image ];
    exact ⟨ ∅, by simp +decide ⟩;
  obtain ⟨ D, hD₁, hD₂ ⟩ := h_max_clique;
  rcases D.eq_empty_or_nonempty with ( rfl | hD₃ ) <;> simp_all +decide;
  · exact ⟨ { hC.choose }, Finset.singleton_subset_iff.mpr hC.choose_spec, by simp +decide [ SimpleGraph.isClique_iff ], Finset.singleton_nonempty _ ⟩;
  · exact ⟨ D, hD₁.1, hD₁.2.1, hD₂, hD₃ ⟩

/-
A clique on `D` has exactly `C(|D|,2)` internal edges.
-/
omit [Fintype V] in
lemma eIn_of_clique (G : SimpleGraph V) (D : Finset V) (hD : G.IsClique (D : Set V)) :
    eIn G D = Nat.choose D.card 2 := by
  convert Finset.card_filter ( fun s => G.IsClique ( s : Set V ) ) ( Finset.powersetCard 2 D );
  rw [ Finset.sum_congr rfl fun x hx => if_pos <| ?_ ];
  · simp +decide [ Finset.card_image_of_injective, Function.Injective ];
  · simp +zetaDelta at *;
    obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hx; exact hD.subset ha₁;

/-
For a chordal graph with maximum clique `A` (`p = |A|`), writing `C = Aᶜ`, `q =
|C|`, the number of edges meeting `C` is at most `q(p-1)`.
-/
lemma edges_outside (G : SimpleGraph V) (hG : IsChordal G) (A : Finset V)
    (hA : IsMaxClique G A) :
    eBetween G A Aᶜ + eIn G Aᶜ ≤ Aᶜ.card * (A.card - 1) := by
  have h_edges : eIn G Finset.univ = G.edgeFinset.card := by
    rw [ eIn_card_eq, Finset.filter_true_of_mem ] ; aesop;
  have h_edges_decomp : G.edgeFinset.card = eIn G A + eBetween G A Aᶜ + eIn G Aᶜ :=
    edges_decomp G A
  have := edges_outside_core G hG Finset.univ A ( Finset.subset_univ _ ) hA.1 ( fun B hB₁ hB₂ => hA.2 B hB₂ ) ; simp_all +decide ;
  simp_all +decide [ Finset.card_compl ] ; linarith

/-
For a chordal graph, a subset `C` and a maximum clique `D` of `G[C]` of order `k
= |D|`, there is a clique partition `R` of the edges inside `C` with `|R| ≤ 1 +
eIn C - C(k,2)` and `|R| ≤ 1 + (q-k)(k-1)`.
-/
lemma relative_partition (G : SimpleGraph V) (hG : IsChordal G) (C D : Finset V)
    (hDsub : D ⊆ C) (hDcl : G.IsClique (D : Set V))
    (hDmax : ∀ B : Finset V, B ⊆ C → G.IsClique (B : Set V) → B.card ≤ D.card)
    (hk : 1 ≤ D.card) :
    ∃ R : Finset (Finset V), IsCliquePartitionOn G C R ∧
      R.card + Nat.choose D.card 2 ≤ 1 + eIn G C ∧
      R.card ≤ 1 + (C.card - D.card) * (D.card - 1) := by
  by_cases hD : D.card = 1;
  · refine' ⟨ ∅, _, _, _ ⟩ <;> simp_all +decide [ IsCliquePartitionOn ];
    intro x y hx hy hxy; specialize hDmax { x, y } ; simp_all +decide [ SimpleGraph.isClique_iff, Finset.insert_subset_iff ] ;
    rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] at hDmax <;> aesop;
  · -- Define the "non-D internal edges" and the part map.
    set S := G.edgeFinset.filter (fun e => (∀ v ∈ e, v ∈ C) ∧ ¬ (∀ v ∈ e, v ∈ D))
    set part : Sym2 V → Finset V := fun e => Finset.univ.filter (fun v => v ∈ e);
    refine' ⟨ Insert.insert D ( S.image part ), _, _, _ ⟩;
    · constructor;
      · simp +zetaDelta at *;
        refine' ⟨ ⟨ hDsub, hDcl, Nat.lt_of_le_of_ne ( Finset.card_pos.mpr hk ) ( Ne.symm hD ) ⟩, _ ⟩;
        rintro a x hx hx' y hy hy' rfl; simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
        rcases x with ⟨ u, v ⟩ ; simp_all +decide ;
        exact Finset.one_lt_card.2 ⟨ u, by aesop, v, by aesop ⟩;
      · intro x y hx hy hxy
        by_cases hxyD : x ∈ D ∧ y ∈ D;
        · refine' ⟨ D, _, _ ⟩ <;> simp_all +decide ;
          simp +zetaDelta at *;
          intro a ha ha' z hz hz' hx hy; have := hDmax { x, y, z } ; simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ] ;
          cases a ; aesop;
        · refine' ⟨ part ( Sym2.mk ( x, y ) ), _, _ ⟩ <;> simp_all +decide [ Finset.mem_image ];
          · simp +zetaDelta at *;
            refine' Or.inr ⟨ Sym2.mk ( x, y ), _, _ ⟩ <;> simp_all +decide ;
            tauto;
          · simp +zetaDelta at *;
            intro a ha ha' x hx hx' hx'' hy''; ext v; simp_all +decide ;
            rcases a with ⟨ u, v ⟩ ; aesop;
    · -- By definition of $S$, we know that $S.card = eIn G C - eIn G D$.
      have hS_card : S.card = eIn G C - eIn G D := by
        rw [ show S = ( G.edgeFinset.filter ( fun e => ∀ v ∈ e, v ∈ C ) ) \ ( G.edgeFinset.filter ( fun e => ∀ v ∈ e, v ∈ D ) ) from ?_, Finset.card_sdiff ];
        · congr 1;
          · rw [ eIn_card_eq ];
          · rw [ eIn_card_eq ];
            exact congr_arg Finset.card ( Finset.ext fun x => by aesop );
        · grind;
      rw [ Finset.card_insert_of_notMem, Finset.card_image_of_injOn ];
      · rw [ hS_card, add_assoc, add_comm ];
        rw [ add_assoc, ← eIn_of_clique G D hDcl ];
        rw [ add_tsub_cancel_of_le ];
        refine' Finset.card_mono _;
        simp +decide [ Finset.subset_iff ];
        exact fun x y hy₁ hy₂ hy₃ hy₄ => ⟨ ⟨ y, ⟨ fun z hz => hDsub ( hy₁ hz ), hy₂ ⟩, hy₃ ⟩, hy₄ ⟩;
      · intro e he e' he' h; simp_all +decide [ Finset.ext_iff, Sym2.ext_iff ] ;
        aesop;
      · grind;
    · -- By edges_outside_core, eIn G C ≤ eIn G D + (C.card - D.card)*(D.card-1), so S.card = eIn G C - eIn G D ≤ (C.card - D.card)*(D.card-1).
      have hS_card : S.card ≤ (C.card - D.card) * (D.card - 1) := by
        have hS_card : S.card = eIn G C - eIn G D := by
          rw [ show S = ( G.edgeFinset.filter ( fun e => ∀ v ∈ e, v ∈ C ) ) \ ( G.edgeFinset.filter ( fun e => ∀ v ∈ e, v ∈ D ) ) from ?_, Finset.card_sdiff ];
          · congr 1;
            · rw [ eIn_card_eq ];
            · rw [ eIn_card_eq ];
              exact congr_arg Finset.card ( Finset.ext fun x => by aesop );
          · grind;
        exact hS_card ▸ Nat.sub_le_of_le_add ( by linarith [ edges_outside_core G hG C D hDsub hDcl hDmax ] );
      grind

/-
Taking the maximum clique `A` as one part and every edge outside `A` singly
gives a clique partition; hence `cp G ≤ 1 + eBetween A C + eIn C`.
-/
lemma cp_le_A_singles (G : SimpleGraph V) (A : Finset V) (hA : IsMaxClique G A) :
    cp G ≤ 1 + eBetween G A Aᶜ + eIn G Aᶜ := by
  by_cases hA_card : 2 ≤ A.card;
  · refine' le_trans ( cp_le_cover G { A } _ _ ) _;
    · exact fun Q hQ => by rw [ Finset.mem_singleton.mp hQ ] ; exact ⟨ hA.1, hA_card ⟩ ;
    · aesop;
    · rw [ show ( Finset.filter ( fun e => ¬∃ Q ∈ ( { A } : Finset ( Finset V ) ), ∀ v ∈ e, v ∈ Q ) G.edgeFinset ) = G.edgeFinset \ ( G.edgeFinset.filter ( fun e => ∀ v ∈ e, v ∈ A ) ) by ext; aesop ] ; rw [ Finset.card_sdiff ];
      rw [ show ( Finset.filter ( fun e => ∀ v ∈ e, v ∈ A ) G.edgeFinset ∩ G.edgeFinset ) = Finset.filter ( fun e => ∀ v ∈ e, v ∈ A ) G.edgeFinset by ext; aesop ] ; rw [ show G.edgeFinset.card = eIn G A + eBetween G A Aᶜ + eIn G Aᶜ by exact edges_decomp G A ▸ by aesop ] ; simp +arith +decide [ eIn_card_eq ] ;
  · interval_cases _ : A.card <;> simp_all +decide [ IsMaxClique ];
    · refine' le_trans ( csInf_le _ ⟨ ∅, _, rfl ⟩ ) _ <;> norm_num [ IsCliquePartition ];
      intro x y hxy; specialize hA; have := hA.2 { x, y } ; simp_all +decide [ SimpleGraph.isClique_iff, Finset.ext_iff ] ;
      exact hA.2 { x } ( by simp +decide ) x ( by simp +decide );
    · -- Since $A$ is a maximum clique of size 1, $G$ has no edges.
      have h_no_edges : G.edgeFinset = ∅ := by
        ext ⟨ u, v ⟩ ; simp +decide ;
        exact fun h => absurd ( hA.2 { u, v } ( by aesop ) ) ( by simp +decide [ h.ne ] );
      refine' le_trans ( csInf_le _ ⟨ ∅, _, rfl ⟩ ) _ <;> simp_all +decide [ IsCliquePartition ]

/-
Taking `A`, every cross edge singly, and a clique partition `R` of the edges
inside `C = Aᶜ` gives `cp G ≤ 1 + eBetween A C + |R|`.
-/
lemma cp_le_A_cross_R (G : SimpleGraph V) (A : Finset V) (hAc : G.IsClique (A : Set V))
    (h2 : 2 ≤ A.card) (R : Finset (Finset V)) (hR : IsCliquePartitionOn G Aᶜ R) :
    cp G ≤ 1 + eBetween G A Aᶜ + R.card := by
  -- Apply the lemma `cp_le_cover` with `𝒬 = insert A R`.
  have h_cover : cp G ≤ (insert A R).card + (G.edgeFinset.filter (fun e => ¬ ∃ Q ∈ insert A R, ∀ v ∈ e, v ∈ Q)).card := by
    convert cp_le_cover G ( insert A R ) _ _;
    · simp_all +decide [ IsCliquePartitionOn ];
    · intro Q₁ hQ₁ Q₂ hQ₂ x y hxy hx hy; cases' Finset.mem_insert.mp hQ₁ with hQ₁ hQ₁ <;> cases' Finset.mem_insert.mp hQ₂ with hQ₂ hQ₂ <;> simp_all +decide ;
      · have := hR.1 Q₂ hQ₂; simp_all +decide [ Finset.subset_iff ] ;
      · have := hR.1 Q₁ hQ₁; simp_all +decide [ Finset.subset_iff ] ;
      · have := hR.2 x y;
        exact this ( hR.1 _ hQ₁ |>.1 hx.1 ) ( hR.1 _ hQ₁ |>.1 hx.2 ) hxy |>.unique ⟨ hQ₁, hx.1, hx.2 ⟩ ⟨ hQ₂, hy.1, hy.2 ⟩;
  -- The edge set {e ∈ G.edgeFinset | ¬ ∃ Q ∈ insert A R, ∀ v ∈ e, v ∈ Q} equals {e ∈ G.edgeFinset | (∃ v ∈ e, v ∈ A) ∧ (∃ v ∈ e, v ∈ Aᶜ)} (cross edges).
  have h_edge_set : G.edgeFinset.filter (fun e => ¬ ∃ Q ∈ insert A R, ∀ v ∈ e, v ∈ Q) = G.edgeFinset.filter (fun e => (∃ v ∈ e, v ∈ A) ∧ (∃ v ∈ e, v ∈ Aᶜ)) := by
    ext e;
    rcases e with ⟨ x, y ⟩ ; simp +decide ;
    intro hxy; by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp +decide [ hx, hy ] ;
    · intro Q hQ; have := hR.1 Q hQ; simp_all +decide [ Finset.subset_iff ] ;
      exact Or.inl fun h => this.1 h hx;
    · intro Q hQ; have := hR.1 Q hQ; simp_all +decide [ SimpleGraph.IsClique ] ;
      exact Or.inr fun h => Finset.mem_compl.mp ( this.1 h ) hy;
    · exact hR.2 x y ( by simpa using hx ) ( by simpa using hy ) hxy |> ExistsUnique.exists;
  -- The cardinality of the set of cross edges is equal to `eBetween G A Aᶜ`.
  have h_card_cross : (G.edgeFinset.filter (fun e => (∃ v ∈ e, v ∈ A) ∧ (∃ v ∈ e, v ∈ Aᶜ))).card = eBetween G A Aᶜ := by
    rw [ eBetween_card_eq ];
    exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_compl.mp hx' hx;
  grind +splitImp

/-
Among `p` nonnegative weights there is a `q`-subset whose total weight is at
least a `q/p` fraction of the whole.
-/
lemma exists_large_subset {p : ℕ} (f : Fin p → ℕ) (q : ℕ) (hq : q ≤ p) :
    ∃ T : Finset (Fin p), T.card = q ∧ q * (∑ i, f i) ≤ p * (∑ i ∈ T, f i) := by
  by_contra! h_contra;
  have h_sum : ∑ T ∈ Finset.powersetCard q (Finset.univ : Finset (Fin p)), ∑ i ∈ T, f i = Nat.choose (p - 1) (q - 1) * ∑ i, f i := by
    have h_sum : ∀ i : Fin p, ∑ T ∈ Finset.powersetCard q (Finset.univ : Finset (Fin p)), (if i ∈ T then f i else 0) = Nat.choose (p - 1) (q - 1) * f i := by
      intro i
      have h_count : Finset.card (Finset.filter (fun T => i ∈ T) (Finset.powersetCard q (Finset.univ : Finset (Fin p)))) = Nat.choose (p - 1) (q - 1) := by
        have h_count : Finset.card (Finset.filter (fun T => i ∈ T) (Finset.powersetCard q (Finset.univ : Finset (Fin p)))) = Finset.card (Finset.powersetCard (q - 1) (Finset.univ \ {i})) := by
          refine' Finset.card_bij ( fun T hT => T.erase i ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
          · intro a₁ ha₁ hi₁ a₂ ha₂ hi₂ h; rw [ ← Finset.insert_erase hi₁, ← Finset.insert_erase hi₂, h ] ;
          · intro b hi hb; use Insert.insert i b; simp_all +decide [ Finset.card_insert_of_notMem ] ;
            rcases q with ( _ | _ | q ) <;> simp_all +decide;
        simp_all +decide [ Finset.card_sdiff ];
      simp_all +decide [ Finset.sum_ite ];
    rw [ Finset.mul_sum _ _ _, ← Finset.sum_congr rfl fun i hi => h_sum i ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  rcases p with ( _ | p ) <;> rcases q with ( _ | q ) <;> simp_all +decide [ mul_comm ];
  have h_sum : ∑ T ∈ Finset.powersetCard (q + 1) (Finset.univ : Finset (Fin (p + 1))), (p + 1) * ∑ i ∈ T, f i < ∑ T ∈ Finset.powersetCard (q + 1) (Finset.univ : Finset (Fin (p + 1))), (∑ i, f i) * (q + 1) := by
    exact Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp ( by simpa using Nat.choose_pos ( by linarith ) ) ) fun T hT => h_contra T ( Finset.mem_powersetCard.mp hT |>.2 );
  simp_all +decide [ ← Finset.mul_sum _ _ _ ];
  nlinarith [ Nat.add_one_mul_choose_eq p q, Nat.choose_succ_succ p q, show 0 ≤ ∑ i, f i from Nat.zero_le _ ]

/-
Choosing a bijection `A ≃ Fin p` and colouring the edge `{a,b}` of `A` by `col a
+ col b` (in `Fin p`) gives `p` colour classes, each a matching, partitioning
all edges of the complete graph on `A`.
-/
lemma exists_color_matchings (A : Finset V) (hA : 0 < A.card) :
    ∃ M : Fin A.card → Finset (Finset V),
      (∀ k, ∀ e ∈ M k, e ⊆ A ∧ e.card = 2) ∧
      (∀ k, ∀ e ∈ M k, ∀ e' ∈ M k, ∀ x, x ∈ e → x ∈ e' → e = e') ∧
      (∀ k k', k ≠ k' → Disjoint (M k) (M k')) ∧
      Finset.univ.biUnion M = A.powersetCard 2 := by
  by_contra h;
  -- Let $p = A.card$ and $g := A.equivFin : {x // x ∈ A} ≃ Fin p$.
  set p := A.card
  have hp : NeZero p := by
    exact ⟨ hA.ne' ⟩
  set g := A.equivFin;
  -- Define a total colouring `col : V → Fin p` by `col v := if h : v ∈ A then g ⟨v, h⟩ else 0`.
  set col : V → Fin p := fun v => if h : v ∈ A then g ⟨v, h⟩ else 0;
  refine' h ⟨ fun k => Finset.filter ( fun e => ∑ a ∈ e, col a = k ) ( Finset.powersetCard 2 A ), _, _, _, _ ⟩;
  · simp +contextual [ Finset.subset_iff ];
  · intro k e he e' he' x hx hx'
    have h_eq : ∀ y ∈ e, y ≠ x → ∀ y' ∈ e', y' ≠ x → col y = col y' := by
      intro y hy hyx y' hy' hy'x
      have h_sum_eq : ∑ a ∈ e, col a = ∑ a ∈ e', col a := by
        grind;
      rw [ Finset.mem_filter ] at he he';
      rw [ Finset.mem_powersetCard ] at he he';
      rw [ Finset.card_eq_two ] at he he';
      grind;
    have h_eq : ∀ y ∈ e, y ≠ x → ∀ y' ∈ e', y' ≠ x → y = y' := by
      intros y hy hyx y' hy' hy'x
      have h_eq_col : col y = col y' := h_eq y hy hyx y' hy' hy'x
      have h_eq_g : g ⟨y, by
        exact Finset.mem_powersetCard.mp ( Finset.mem_filter.mp he |>.1 ) |>.1 hy⟩ = g ⟨y', by
        exact Finset.mem_powersetCard.mp ( Finset.mem_filter.mp he' |>.1 ) |>.1 hy'⟩ := by
        grind
      have h_eq_y : y = y' := by
        exact congr_arg Subtype.val ( g.injective h_eq_g )
      exact h_eq_y;
    simp +zetaDelta at *;
    obtain ⟨ y, hy ⟩ := Finset.exists_mem_ne ( by linarith ) x;
    rw [ Finset.card_eq_two ] at he he';
    grind;
  · simp +contextual [ Finset.disjoint_left ];
  · ext e; simp [col]

/-
For disjoint vertex sets `A`, `C`, there is a family `Tri` of triangles, each
consisting of an edge of `A` together with a vertex of `C`, that are pairwise
edge-disjoint, and large enough that `C(p,2) + p·q ≤ 2·|Tri| + hsplit p q` (with
`p = |A|`, `q = |C|`).  The triangles arise by assigning the (near-)perfect
matchings of the complete graph on `A` to distinct vertices of `C`.
-/
lemma exists_triangles (A C : Finset V) (hAC : Disjoint A C) :
    ∃ Tri : Finset (Finset V),
      (∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ C ∧ t = {u, v, c}) ∧
      (∀ t₁ ∈ Tri, ∀ t₂ ∈ Tri, ∀ x y, x ≠ y → x ∈ t₁ → y ∈ t₁ → x ∈ t₂ → y ∈ t₂ →
        t₁ = t₂) ∧
      A.card.choose 2 + A.card * C.card ≤ 2 * Tri.card + hsplit A.card C.card := by
  by_cases hA : 0 < A.card;
  · obtain ⟨M, hM1, hM2, hM3, hM4⟩ := exists_color_matchings A hA;
    obtain ⟨K, hK⟩ : ∃ K : Finset (Fin A.card), K.card = min C.card A.card ∧ min C.card A.card * (∑ k, (M k).card) ≤ A.card * (∑ k ∈ K, (M k).card) := by
      convert exists_large_subset ( fun k => ( M k |> Finset.card ) ) ( min C.card A.card ) ( min_le_right _ _ ) using 1;
    obtain ⟨apex, hapex⟩ : ∃ apex : Fin A.card → V, (∀ k ∈ K, apex k ∈ C) ∧ (∀ k₁ k₂, k₁ ∈ K → k₂ ∈ K → k₁ ≠ k₂ → apex k₁ ≠ apex k₂) := by
      obtain ⟨f, hf⟩ : ∃ f : Fin K.card → V, (∀ i, f i ∈ C) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
        have h_inj : ∃ f : Fin K.card → V, Function.Injective f ∧ ∀ i, f i ∈ C := by
          have h_card : K.card ≤ C.card := by
            exact hK.1.symm ▸ min_le_left _ _
          have := Finset.exists_subset_card_eq h_card;
          obtain ⟨ t, ht₁, ht₂ ⟩ := this;
          have h_inj : Nonempty (Fin K.card ≃ t) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ ht₂ ] ⟩;
          exact ⟨ _, Subtype.val_injective.comp h_inj.some.injective, fun i => ht₁ <| h_inj.some i |>.2 ⟩;
        exact ⟨ h_inj.choose, h_inj.choose_spec.2, fun i j hij => h_inj.choose_spec.1.ne hij ⟩;
      obtain ⟨g, hg⟩ : ∃ g : Fin K.card ≃ K, True := by
        exact ⟨ Fintype.equivOfCardEq ( by simp +decide [ hK.1 ] ), trivial ⟩;
      use fun k => if hk : k ∈ K then f ( g.symm ⟨ k, hk ⟩ ) else Classical.choose ( Finset.card_pos.mp ( by linarith [ Finset.card_pos.mpr ⟨ Classical.choose ( Finset.card_pos.mp hA ), Classical.choose_spec ( Finset.card_pos.mp hA ) ⟩ ] ) );
      simp +contextual [ hf ];
    refine' ⟨ Finset.biUnion K fun k => Finset.image ( fun e => Insert.insert ( apex k ) e ) ( M k ), _, _, _ ⟩;
    · simp +zetaDelta at *;
      rintro t k hk e he rfl;
      obtain ⟨ u, v, hu, hv, huv ⟩ := Finset.card_eq_two.mp ( hM1 k e he |>.2 );
      exact ⟨ u, hM1 k _ he |>.1 ( by simp +decide ), v, hM1 k _ he |>.1 ( by simp +decide ), hu, apex k, hapex.1 k hk, by simp +decide [ *, Finset.Subset.antisymm_iff, Finset.subset_iff ] ⟩;
    · simp +contextual [ Finset.mem_biUnion ];
      rintro t₁ k₁ hk₁ e₁ he₁ rfl t₂ k₂ hk₂ e₂ he₂ rfl x y hxy hx hy hx' hy';
      -- If $x$ and $y$ are both in $A$, then $k₁ = k₂$ and $e₁ = e₂$.
      by_cases hx_A : x ∈ A
      by_cases hy_A : y ∈ A;
      · have h_eq : e₁ = e₂ := by
          have h_eq : x ∈ e₁ ∧ y ∈ e₁ ∧ x ∈ e₂ ∧ y ∈ e₂ := by
            simp_all +decide [ Finset.disjoint_left ];
            grind;
          have := hM1 k₁ e₁ he₁; have := hM1 k₂ e₂ he₂; simp_all +decide [ Finset.card_eq_two ] ;
          grind;
        specialize hM3 k₁ k₂ ; simp_all +decide [ Finset.disjoint_left ];
        grind;
      · grind;
      · grind;
    · -- By definition of $Tri$, we know that its cardinality is at least the sum of the cardinalities of the matchings in $K$.
      have hTri_card : (Finset.biUnion K (fun k => Finset.image (fun e => Insert.insert (apex k) e) (M k))).card ≥ ∑ k ∈ K, (M k).card := by
        rw [ Finset.card_biUnion ];
        · refine' Finset.sum_le_sum fun k hk => Finset.card_image_of_injOn _ |> ge_of_eq;
          intro e he e' he' h; simp_all +decide [ Finset.ext_iff ] ;
          intro a; specialize h a; by_cases ha : a = apex k <;> simp_all +decide ;
          exact iff_of_false ( fun h => Finset.disjoint_left.mp hAC ( hM1 k e he |>.1 h ) ( hapex.1 k hk ) ) ( fun h => Finset.disjoint_left.mp hAC ( hM1 k e' he' |>.1 h ) ( hapex.1 k hk ) );
        · intro k hk k' hk' hkk'; simp_all +decide [ Finset.disjoint_left ] ;
          intro e he e' he' h; have := Finset.ext_iff.mp h ( apex k ) ; have := Finset.ext_iff.mp h ( apex k' ) ; simp_all +decide ;
          replace h := Finset.ext_iff.mp h ( apex k ) ; simp_all +decide [ Finset.subset_iff ] ;
          exact hAC ( hM1 _ _ he' |>.1 h ) ( hapex.1 _ hk );
      have h_sum_card : ∑ k, (M k).card = Nat.choose A.card 2 := by
        rw [ ← Finset.card_biUnion ];
        · rw [ hM4, Finset.card_powersetCard ];
        · exact fun i _ j _ hij => hM3 i j hij;
      unfold hsplit; split_ifs <;> simp_all +decide [ Nat.choose_two_right ] ;
      · nlinarith [ Nat.div_mul_cancel ( show 2 ∣ A.card * ( A.card - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ), Nat.sub_add_cancel ( show 1 ≤ A.card from Finset.card_pos.mpr hA ) ];
      · simp_all +decide [ min_eq_right ( le_of_lt ‹_› ) ];
        grind;
  · use ∅; aesop;

/-
Lower bound on the number of surviving triangles (those that remain cliques
in `G`): the non-surviving ones inject into the absent cross pairs.
-/
lemma triangle_survivors_lb (G : SimpleGraph V) (A : Finset V) (hAc : G.IsClique (A : Set V))
    (Tri : Finset (Finset V))
    (hstruct : ∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ Aᶜ ∧ t = {u, v, c})
    (hdisj : ∀ t₁ ∈ Tri, ∀ t₂ ∈ Tri, ∀ x y, x ≠ y → x ∈ t₁ → y ∈ t₁ → x ∈ t₂ → y ∈ t₂ →
        t₁ = t₂) :
    Tri.card ≤ (Tri.filter (fun t => G.IsClique (t : Set V))).card
      + (A.card * Aᶜ.card - eBetween G A Aᶜ) := by
  -- Let $S$ be the set of triangles in $Tri$ that are cliques in $G$, and let $N$ be the set of triangles in $Tri$ that are not cliques in $G$.
  set S := Tri.filter (fun t => G.IsClique (t : Set V))
  set N := Tri.filter (fun t => ¬G.IsClique (t : Set V));
  -- By definition of $S$ and $N$, we have $Tri.card = S.card + N.card$.
  have h_card : Tri.card = S.card + N.card := by
    rw [ Finset.card_filter_add_card_filter_not ];
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide;
  -- By definition of $N$, we have $N.card \leq \sum_{t \in N} |\{ (u, c) \in A \times A^c \mid \neg G.Adj u c \}|$.
  have hN_card : N.card ≤ Finset.card (Finset.filter (fun p => ¬G.Adj p.1 p.2) (A ×ˢ Aᶜ)) := by
    have hN_card : N.card ≤ Finset.card (Finset.biUnion N (fun t => Finset.filter (fun p => p.1 ∈ t ∧ p.2 ∈ t ∧ ¬G.Adj p.1 p.2) (A ×ˢ Aᶜ))) := by
      rw [ Finset.card_biUnion ];
      · refine' le_trans _ ( Finset.sum_le_sum fun t ht => Finset.card_pos.mpr _ );
        · simp +decide;
        · simp +zetaDelta at *;
          rcases ht with ⟨ ⟨ a, ha, rfl ⟩, ht ⟩;
          obtain ⟨ u, hu, v, hv, huv, w, hw, rfl ⟩ := hstruct a ha;
          contrapose! ht;
          simp_all +decide [ Finset.ext_iff, Set.Pairwise ];
      · intros t ht t' ht' h; simp_all +decide [ Finset.disjoint_left ] ;
        simp +zetaDelta at *;
        grind +ring;
    exact hN_card.trans ( Finset.card_le_card fun p hp => by aesop );
  rw [ Finset.filter_not, Finset.card_sdiff ] at hN_card ; simp_all +decide [ Finset.card_product ];
  convert hN_card using 2;
  exact congr_arg Finset.card ( by ext; aesop )

/-
Lower bound on the number of `G`-edges covered by `R ∪ (surviving triangles)`:
the `eIn G Aᶜ` inside-`Aᶜ` edges (covered by `R`) plus three per surviving
triangle.
-/
lemma triangle_covered_lb (G : SimpleGraph V) (A : Finset V) (R : Finset (Finset V))
    (hR : IsCliquePartitionOn G Aᶜ R)
    (Tri : Finset (Finset V))
    (hstruct : ∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ Aᶜ ∧ t = {u, v, c})
    (hdisj : ∀ t₁ ∈ Tri, ∀ t₂ ∈ Tri, ∀ x y, x ≠ y → x ∈ t₁ → y ∈ t₁ → x ∈ t₂ → y ∈ t₂ →
        t₁ = t₂) :
    eIn G Aᶜ + 3 * (Tri.filter (fun t => G.IsClique (t : Set V))).card ≤
      (G.edgeFinset.filter (fun e =>
        ∃ Q ∈ R ∪ Tri.filter (fun t => G.IsClique (t : Set V)), ∀ v ∈ e, v ∈ Q)).card := by
  refine' le_trans _ ( Finset.card_mono _ );
  rotate_left;
  exact Finset.biUnion ( Finset.filter ( fun t : Finset V => G.IsClique ( t : Set V ) ) Tri ) ( fun t => Finset.filter ( fun e => ¬e.IsDiag ) ( Finset.image ( fun p : V × V => s(p.1, p.2) ) ( Finset.offDiag t ) ) ) ∪ Finset.filter ( fun e => ∀ v ∈ e, v ∈ Aᶜ ) G.edgeFinset;
  · intro e he; simp_all +decide ;
    rcases he with ( ⟨ t, ht, ⟨ u, v, ⟨ hu, hv, huv ⟩, rfl ⟩, he ⟩ | ⟨ he, he' ⟩ );
    · exact ⟨ ht.2 hu hv huv, t, Or.inr ⟨ ht.1, ht.2 ⟩, by simp +decide [ hu, hv ] ⟩;
    · rcases e with ⟨ u, v ⟩ ; simp_all +decide [ IsCliquePartitionOn ] ;
      exact ExistsUnique.exists ( hR.2 u v he'.1 he'.2 he ) |> fun ⟨ Q, hQ ⟩ => ⟨ Q, Or.inl hQ.1, hQ.2.1, hQ.2.2 ⟩;
  · rw [ Finset.card_union_of_disjoint, Finset.card_biUnion ];
    · rw [ add_comm ];
      refine' add_le_add _ _;
      · refine' le_trans _ ( Finset.sum_le_sum fun t ht => show Finset.card _ ≥ 3 from _ );
        · simp +decide [ mul_comm ];
          convert rfl.le;
          rw [ Finset.card_filter, Finset.card_filter ];
          refine' Finset.sum_bij ( fun t ht => t ) _ _ _ _ <;> simp +decide;
        · obtain ⟨ u, v, c, hu, hv, huv, hc, rfl ⟩ := hstruct t ( Finset.filter_subset _ _ ht ) ; simp +decide [ *, Finset.filter ] ;
          by_cases hu' : u = c <;> by_cases hv' : v = c <;> simp +decide [hu', hv'] at hc ⊢;
          · grind;
          · grind;
          · grind;
          · erw [ Multiset.coe_card ] ; simp +decide [ *, List.offDiag ] ;
            simp +decide [ List.filter_cons ];
            grind;
      · rw [ eIn_card_eq ];
    · intro t₁ ht₁ t₂ ht₂ hne; simp_all +decide [ Finset.disjoint_left ] ;
      grind;
    · simp +contextual [ Finset.disjoint_left ];
      grind +qlia

/-
The family `R ∪ (surviving triangles)` consists of cliques of order ≥ 2.
-/
lemma triangle_family_clique (G : SimpleGraph V) (A : Finset V)
    (R : Finset (Finset V)) (hR : IsCliquePartitionOn G Aᶜ R)
    (Tri : Finset (Finset V))
    (hstruct : ∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ Aᶜ ∧ t = {u, v, c}) :
    ∀ Q ∈ R ∪ Tri.filter (fun t => G.IsClique (t : Set V)),
      G.IsClique (Q : Set V) ∧ 2 ≤ Q.card := by
  intro Q hQ
  cases' Finset.mem_union.mp hQ with hQ_R hQ_Tri
  ·
    exact hR.1 Q hQ_R |>.2
  ·
    grind +revert

/-
Each `G`-edge lies in at most one member of `R ∪ (surviving triangles)`.
-/
lemma triangle_family_disj (G : SimpleGraph V) (A : Finset V)
    (R : Finset (Finset V)) (hR : IsCliquePartitionOn G Aᶜ R)
    (Tri : Finset (Finset V))
    (hstruct : ∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ Aᶜ ∧ t = {u, v, c})
    (hdisj : ∀ t₁ ∈ Tri, ∀ t₂ ∈ Tri, ∀ x y, x ≠ y → x ∈ t₁ → y ∈ t₁ → x ∈ t₂ → y ∈ t₂ →
        t₁ = t₂) :
    ∀ Q₁ ∈ R ∪ Tri.filter (fun t => G.IsClique (t : Set V)),
      ∀ Q₂ ∈ R ∪ Tri.filter (fun t => G.IsClique (t : Set V)), ∀ x y, G.Adj x y →
        (x ∈ Q₁ ∧ y ∈ Q₁) → (x ∈ Q₂ ∧ y ∈ Q₂) → Q₁ = Q₂ := by
  intro Q₁ hQ₁ Q₂ hQ₂ x y hxy hx hy;
  by_cases hQ₁R : Q₁ ∈ R <;> by_cases hQ₂R : Q₂ ∈ R <;> simp +decide [ hQ₁R, hQ₂R ] at hQ₁ hQ₂ ⊢;
  · have := hR.2 x y;
    exact ExistsUnique.unique ( this ( hR.1 _ hQ₁R |>.1 hx.1 ) ( hR.1 _ hQ₁R |>.1 hx.2 ) hxy ) ⟨ hQ₁R, hx.1, hx.2 ⟩ ⟨ hQ₂R, hy.1, hy.2 ⟩;
  · have hQ₁_subset_Ac : Q₁ ⊆ Aᶜ := by
      exact hR.1 _ hQ₁R |>.1;
    obtain ⟨ u, v, c, hu, hv, huv, hc, rfl ⟩ := hstruct _ hQ₂.1; simp_all +decide [ Finset.subset_iff ] ;
    grind +suggestions;
  · obtain ⟨ u, v, c, hu, hv, huv, hc, rfl ⟩ := hstruct _ hQ₁.1;
    have := hR.1 _ hQ₂R; simp_all +decide [ Finset.subset_iff ] ;
    grind +suggestions;
  · exact hdisj _ hQ₁.1 _ hQ₂.1 _ _ hxy.ne hx.1 hx.2 hy.1 hy.2

/-
Given a family of edge-disjoint triangles (edge of `A` + vertex of `C = Aᶜ`)
with the size bound of `exists_triangles`, and a clique partition `R` of the
edges inside `Aᶜ`, the covering bound `cp_le_cover` yields the construction-(c)
bound.
-/
lemma cp_le_split_of_triangles (G : SimpleGraph V) (A : Finset V)
    (hAc : G.IsClique (A : Set V)) (R : Finset (Finset V))
    (hR : IsCliquePartitionOn G Aᶜ R)
    (Tri : Finset (Finset V))
    (hstruct : ∀ t ∈ Tri, ∃ u v c, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ c ∈ Aᶜ ∧ t = {u, v, c})
    (hdisj : ∀ t₁ ∈ Tri, ∀ t₂ ∈ Tri, ∀ x y, x ≠ y → x ∈ t₁ → y ∈ t₁ → x ∈ t₂ → y ∈ t₂ →
        t₁ = t₂)
    (hsize : A.card.choose 2 + A.card * Aᶜ.card ≤ 2 * Tri.card + hsplit A.card Aᶜ.card) :
    cp G ≤ hsplit A.card Aᶜ.card + (A.card * Aᶜ.card - eBetween G A Aᶜ) + R.card := by
  refine' le_trans _ ( _ : _ ≤ _ );
  exact R.card + ( Tri.filter ( fun t => G.IsClique ( t : Set V ) ) ).card + ( A.card.choose 2 + eBetween G A Aᶜ + eIn G Aᶜ - ( eIn G Aᶜ + 3 * ( Tri.filter ( fun t => G.IsClique ( t : Set V ) ) ).card ) );
  · refine' le_trans ( cp_le_cover G ( R ∪ Tri.filter ( fun t => G.IsClique ( t : Set V ) ) ) _ _ ) _;
    · exact fun Q hQ => triangle_family_clique G A R hR Tri hstruct Q hQ;
    · apply_rules [ triangle_family_disj ];
    · rw [ show ( { e ∈ G.edgeFinset | ¬∃ Q ∈ R ∪ { t ∈ Tri | G.IsClique t }, ∀ v ∈ e, v ∈ Q } : Finset ( Sym2 V ) ) = G.edgeFinset \ ( G.edgeFinset.filter ( fun e => ∃ Q ∈ R ∪ { t ∈ Tri | G.IsClique t }, ∀ v ∈ e, v ∈ Q ) ) from ?_ ];
      · rw [ Finset.card_sdiff ];
        gcongr;
        · convert Finset.card_union_le _ _ using 2;
          convert Finset.card_image_of_injective _ Finset.coe_injective using 2 ; aesop;
        · convert edges_decomp G A |> le_of_eq using 1;
          rw [ eIn_of_clique G A hAc ];
        · convert triangle_covered_lb G A R hR Tri hstruct hdisj using 1;
          rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ];
      · grind;
  · rw [ ← Nat.add_sub_assoc ];
    · rw [ tsub_le_iff_right ] ; ring_nf at * ; norm_cast at * ; simp_all +decide [ Nat.choose_two_right ] ;
      have h_card_filter : (Tri.filter (fun t => G.IsClique (t : Set V))).card ≥ Tri.card - (A.card * Aᶜ.card - eBetween G A Aᶜ) := by
        have := triangle_survivors_lb G A hAc Tri ( fun t ht => by
          rcases hstruct t ht with ⟨ u, hu, v, hv, huv, c, hc, rfl ⟩ ; exact ⟨ u, v, c, hu, hv, huv, by simpa using hc, rfl ⟩ ; ) ( fun t₁ ht₁ t₂ ht₂ x y hxy hx hy hx' hy' => hdisj t₁ ht₁ t₂ ht₂ x y hxy hx hy hx' hy' ) ; simp_all +decide ;
      simp +zetaDelta at *;
      linarith [ Nat.sub_add_cancel ( show eBetween G A Aᶜ ≤ A.card * Aᶜ.card from eBetween_le_mul G A Aᶜ ) ];
    · convert triangle_covered_lb G A R hR Tri hstruct hdisj |> le_trans <| ?_ using 1;
      refine' le_trans ( Finset.card_filter_le _ _ ) _;
      rw [ edges_decomp G A, eIn_of_clique G A hAc ]

/-- Using the split-graph edge–triangle partition of `J(A,C)`, deleting the
  absent cross edges, and adjoining a clique partition `R` of the edges inside
  `C = Aᶜ` gives `cp G ≤ hsplit p q + (pq - eBetween A C) + |R|`. -/
lemma cp_le_split (G : SimpleGraph V) (A : Finset V) (hAc : G.IsClique (A : Set V))
    (R : Finset (Finset V)) (hR : IsCliquePartitionOn G Aᶜ R) :
    cp G ≤ hsplit A.card Aᶜ.card + (A.card * Aᶜ.card - eBetween G A Aᶜ) + R.card := by
  obtain ⟨Tri, hstruct, hdisj, hsize⟩ :=
    exists_triangles A Aᶜ (by simp [Finset.disjoint_right])
  exact cp_le_split_of_triangles G A hAc R hR Tri hstruct hdisj hsize

/-!
With `P(X) = 41 X⁴ + 284 X³ + 262 X² + 60 X - 7`, let `θ` be its unique positive
zero, and `τ = (5θ²+2θ+1)/(7θ+5)`, `Γ = θ² + τ²/2`, `c₀ = Γ/4`.
-/

/-- The quartic `P(X) = 41 X⁴ + 284 X³ + 262 X² + 60 X - 7`. -/
noncomputable def Ppoly (X : ℝ) : ℝ := 41 * X ^ 4 + 284 * X ^ 3 + 262 * X ^ 2 + 60 * X - 7

/-
`P` has a unique zero in the interval `(0, 2/23)`.
-/
lemma theta_exists_unique : ∃! x : ℝ, (0 < x ∧ x < 2 / 23) ∧ Ppoly x = 0 := by
  apply_rules [ existsUnique_of_exists_of_unique ];
  · apply_rules [ intermediate_value_Ioo ] <;> norm_num [ Ppoly ];
    exact Continuous.continuousOn ( by unfold Ppoly; continuity );
  · unfold Ppoly;
    exact fun y₁ y₂ h₁ h₂ => le_antisymm ( le_of_not_gt fun h => by nlinarith [ mul_pos ( sub_pos.2 h ) ( sub_pos.2 h₁.1.1 ), mul_pos ( sub_pos.2 h ) ( sub_pos.2 h₂.1.1 ), pow_pos ( sub_pos.2 h ) 3 ] ) ( le_of_not_gt fun h => by nlinarith [ mul_pos ( sub_pos.2 h ) ( sub_pos.2 h₁.1.1 ), mul_pos ( sub_pos.2 h ) ( sub_pos.2 h₂.1.1 ), pow_pos ( sub_pos.2 h ) 3 ] )

/-- The unique positive zero `θ` of `P`. -/
noncomputable def theta : ℝ := (theta_exists_unique).choose

lemma theta_spec : (0 < theta ∧ theta < 2 / 23) ∧ Ppoly theta = 0 :=
  (theta_exists_unique).choose_spec.1

lemma theta_pos : 0 < theta := theta_spec.1.1

lemma theta_lt : theta < 2 / 23 := theta_spec.1.2

lemma Ppoly_theta : Ppoly theta = 0 := theta_spec.2

/-- `τ = (5θ²+2θ+1)/(7θ+5)`. -/
noncomputable def tau : ℝ := (5 * theta ^ 2 + 2 * theta + 1) / (7 * theta + 5)

/-- `Γ = θ² + τ²/2`. -/
noncomputable def Gamma : ℝ := theta ^ 2 + tau ^ 2 / 2

/-- `c₀ = Γ/4`. -/
noncomputable def c0 : ℝ := Gamma / 4

lemma Gamma_pos : 0 < Gamma := by
  exact add_pos_of_pos_of_nonneg ( sq_pos_of_pos ( theta_pos ) ) ( div_nonneg ( sq_nonneg _ ) zero_le_two )

lemma Gamma_lt : Gamma < 1 / 32 := by
  unfold Gamma;
  rw [ show tau = ( 5 * theta ^ 2 + 2 * theta + 1 ) / ( 7 * theta + 5 ) by rfl ];
  rw [ div_pow, div_div, add_div', div_lt_iff₀ ];
  · nlinarith [ mul_pos ( sub_pos_of_lt ( theta_spec.1.2 ) ) ( sub_pos_of_lt ( theta_spec.1.1 ) ), Ppoly_theta, pow_pos ( sub_pos_of_lt ( theta_spec.1.2 ) ) 3, pow_pos ( sub_pos_of_lt ( theta_spec.1.1 ) ) 3 ];
  · exact mul_pos ( sq_pos_of_pos ( by linarith [ theta_pos ] ) ) zero_lt_two;
  · exact mul_ne_zero ( pow_ne_zero 2 ( by linarith [ theta_pos ] ) ) two_ne_zero

/-
A rational lower bound for `θ`: `0.0834 ≤ θ`.
-/
lemma theta_ge : (417 : ℝ) / 5000 ≤ theta := by
  by_contra h;
  have hp := theta_pos; have h0 := Ppoly_theta; unfold Ppoly at h0; nlinarith [ pow_pos hp 3, pow_pos hp 2, pow_pos ( sub_pos.2 <| lt_of_not_ge h ) 3, pow_pos ( sub_pos.2 <| lt_of_not_ge h ) 2, mul_pos ( sub_pos.2 <| lt_of_not_ge h ) hp ] ;

/-
A lower bound for `Γ`: `4/133 ≤ Γ`.
-/
lemma Gamma_ge : (4 : ℝ) / 133 ≤ Gamma := by
  -- By definition of Gamma, we have Gamma = theta^2 + tau^2 / 2.
  unfold Gamma;
  rw [ show tau = ( 5 * theta ^ 2 + 2 * theta + 1 ) / ( 7 * theta + 5 ) by rfl ];
  rw [ div_pow, div_div, add_div', le_div_iff₀ ] <;> try nlinarith [ theta_pos ];
  nlinarith [ theta_ge, theta_lt, pow_pos ( sub_pos.mpr theta_lt ) 3, pow_pos ( sub_pos.mpr theta_lt ) 4 ]

/-- A lower bound for `c₀`: `1/133 ≤ c₀`. -/
lemma c0_ge : (1 : ℝ) / 133 ≤ c0 := by
  unfold c0; linarith [ Gamma_ge ]

lemma positive_analytic (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ Real.sqrt Gamma) :
    a + 7 / 2 * a ^ 2 + 2 * Real.sqrt 2 * (1 - a) * Real.sqrt (Gamma - a ^ 2)
      ≤ 1 / 2 + 2 * Gamma := by
  -- Set $s := \sqrt{\Gamma - a^2}$ and $t := \sqrt{1/25 - a^2}$.
  set s := Real.sqrt (Gamma - a^2)
  set t := Real.sqrt (1 / 25 - a^2);
  -- From Step A: show $2\sqrt{2}(1-a)s - 2\Gamma \le 2\sqrt{2}(1-a)t - 2(1/25)$.
  have h_stepA : 2 * Real.sqrt 2 * (1 - a) * s - 2 * Gamma ≤ 2 * Real.sqrt 2 * (1 - a) * t - 2 * (1 / 25) := by
    have h_stepA : (t - s) * (2 * Real.sqrt 2 * (1 - a) - 2 * (t + s)) ≥ 0 := by
      refine mul_nonneg ?_ ?_;
      · exact sub_nonneg_of_le <| Real.sqrt_le_sqrt <| by linarith [ show Gamma ≤ 1 / 25 by linarith [ Gamma_lt ] ] ;
      · -- Since $t \leq 1/5$ and $s \leq 1/5$, we have $t + s \leq 2/5$.
        have h_ts_le : t + s ≤ 2 / 5 := by
          linarith [ show t ≤ 1 / 5 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩, show s ≤ 1 / 5 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ show Gamma ≤ 1 / 25 by exact le_trans ( le_of_lt ( Gamma_lt ) ) ( by norm_num ) ] ⟩ ];
        nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show a ≤ 1 / 5 by exact le_trans ha' <| Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith [ Gamma_lt ] ⟩ ];
    nlinarith [ Real.mul_self_sqrt ( show 0 ≤ Gamma - a ^ 2 by exact sub_nonneg_of_le <| by nlinarith [ Real.mul_self_sqrt Gamma_pos.le ] ), Real.mul_self_sqrt ( show 0 ≤ 1 / 25 - a ^ 2 by exact sub_nonneg_of_le <| by nlinarith [ Real.mul_self_sqrt Gamma_pos.le, Real.mul_self_sqrt ( show 0 ≤ 1 / 25 by norm_num ), Gamma_lt ] ) ];
  -- From Step B: show $2\sqrt{2}(1-a)t \le 29/50 - a - 7/2*a^2$.
  have h_stepB : 2 * Real.sqrt 2 * (1 - a) * t ≤ 29 / 50 - a - 7 / 2 * a ^ 2 := by
    -- Squaring both sides to remove the square roots.
    suffices h_sq : (2 * Real.sqrt 2 * (1 - a) * t) ^ 2 ≤ (29 / 50 - a - 7 / 2 * a ^ 2) ^ 2 by
      contrapose! h_sq; gcongr;
      nlinarith [ show a ≤ 1 / 5 by exact ha'.trans <| Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith [ show Gamma < 1 / 25 by exact lt_of_lt_of_le ( show Gamma < 1 / 32 by exact Gamma_lt ) <| by norm_num ] ⟩ ];
    rw [ mul_pow, mul_pow, Real.sq_sqrt ] <;> norm_num;
    · norm_num [ mul_pow ];
      nlinarith only [ sq_nonneg ( 15 * a - 1 ), sq_nonneg ( a - 1 / 5 ) ];
    · exact le_trans ( pow_le_pow_left₀ ha ha' 2 ) ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ Gamma by exact le_of_lt Gamma_pos ), Gamma_lt ] );
  grind

/-- The negative branch. -/
lemma negative_analytic (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ Real.sqrt Gamma) :
    x + 3 / 2 * x ^ 2 + 2 * Real.sqrt 2 * (1 + x) * Real.sqrt (Gamma - x ^ 2)
      ≤ 1 / 2 + 2 * Gamma := by
  -- Let R := 1/2 + 2Γ - x - 3/2*x^2. Then R > 6/25 > 0 (since 0 ≤ x ≤ 1/5 and Γ > 0): nlinarith.
  set R : ℝ := 1 / 2 + 2 * Gamma - x - 3 / 2 * x ^ 2
  have hR_pos : 0 < R := by
    -- Since $0 \le x \le \sqrt{\Gamma}$ and $\Gamma < 1/32$, we have $x \le 1/5$.
    have hx_le_1_5 : x ≤ 1 / 5 := by
      exact hx'.trans ( Real.sqrt_le_iff.mpr ⟨ by norm_num, by linarith [ Gamma_lt ] ⟩ );
    exact sub_pos_of_lt ( by nlinarith [ show Gamma > 0 from Gamma_pos ] );
  -- KEY inequality: R² - 8 * (1 + x)² * (Γ - x²) ≥ 0.
  have h_KEY : R ^ 2 - 8 * (1 + x) ^ 2 * (Gamma - x ^ 2) ≥ 0 := by
    -- Use the closed form hΓ : Gamma = theta^2 + (5*theta^2+2*theta+1)^2/(2*(7*theta+5)^2) (unfold Gamma tau; field_simp; ring).
    have hΓ : Gamma = theta^2 + (5 * theta^2 + 2 * theta + 1)^2 / (2 * (7 * theta + 5)^2) := by
      unfold Gamma tau; field_simp
    -- Substitute (rw [hΓ]). Let d := 7*theta+5 > 0 (from theta_pos).
    set d : ℝ := 7 * theta + 5
    have hd_pos : 0 < d := by
      exact add_pos_of_nonneg_of_pos ( mul_nonneg ( by norm_num ) ( le_of_lt ( theta_pos ) ) ) ( by norm_num )
    field_simp [hΓ, hd_pos] at *;
    -- There is the algebraic identity (valid using Ppoly_theta : Ppoly theta = 0):
    --   R² - 8*(1+x)²*(Γ-x²) = (x-theta)²/(4*(7*theta+5)²) * BR,
    -- where BR = (2009*theta²+2870*theta+1025)*x² + (4018*theta³+9464*theta²+7370*theta+1900)*x + (2583*theta⁴+11578*theta³+13393*theta²+5788*theta+722).
    have h_identity : (R ^ 2 - 8 * (1 + x) ^ 2 * (Gamma - x ^ 2)) * 4 * d ^ 2 = (x - theta) ^ 2 * ((2009 * theta ^ 2 + 2870 * theta + 1025) * x ^ 2 + (4018 * theta ^ 3 + 9464 * theta ^ 2 + 7370 * theta + 1900) * x + (2583 * theta ^ 4 + 11578 * theta ^ 3 + 13393 * theta ^ 2 + 5788 * theta + 722)) := by
      have hPpoly_theta : 41 * theta ^ 4 + 284 * theta ^ 3 + 262 * theta ^ 2 + 60 * theta - 7 = 0 := by
        exact Ppoly_theta;
      grind;
    contrapose! h_identity;
    exact ne_of_lt ( lt_of_lt_of_le ( mul_neg_of_neg_of_pos ( mul_neg_of_neg_of_pos h_identity ( by positivity ) ) ( by positivity ) ) ( mul_nonneg ( sq_nonneg _ ) ( by nlinarith only [ hx, hx', theta_pos, theta_lt, pow_pos theta_pos 3, pow_pos theta_pos 4 ] ) ) );
  -- From 0 ≤ LHS, 0 ≤ R, and LHS² ≤ R², conclude LHS ≤ R:
  have h_LHS_le_R : 2 * Real.sqrt 2 * (1 + x) * Real.sqrt (Gamma - x ^ 2) ≤ R := by
    contrapose! h_KEY;
    convert sub_neg_of_lt ( pow_lt_pow_left₀ h_KEY ( by positivity ) two_ne_zero ) using 1 ; ring_nf ; norm_num;
    rw [ Real.sq_sqrt (show (0:ℝ) ≤ -x ^ 2 + Gamma by nlinarith [ Real.mul_self_sqrt Gamma_pos.le ]) ]; ring
  grind +splitImp

/-- The quadratic bound `M(a,b)`. -/
noncomputable def Mbound (a b : ℝ) : ℝ :=
  let al := (1 + a) / 2
  let be := (1 - a) / 2
  if 0 ≤ a then
    1 / 2 * (al ^ 2 / 2 + al * be + 2 * b * (be - b))
  else
    1 / 2 * (al * be - al ^ 2 / 2 + al * be + 2 * b * (be - b))

/-- The quadratic estimate. -/
lemma quadratic_estimate (a : ℝ) (ha : -Real.sqrt Gamma ≤ a) (ha' : a ≤ Real.sqrt Gamma) :
    Mbound a (Real.sqrt ((Gamma - a ^ 2) / 2)) ≤ (1 - Gamma) / 4 := by
  by_cases ha_nonneg : 0 ≤ a;
  · have := positive_analytic a ha_nonneg ( by linarith ) ; unfold Mbound; ring_nf at *; norm_num at *;
    rw [ show - ( a ^ 2 * ( 1 / 2 ) ) + Gamma * ( 1 / 2 ) = ( -a ^ 2 + Gamma ) / 2 by ring ] ; rw [ Real.sqrt_div' ] <;> norm_num ; ring_nf at * ; norm_num at *;
    rw [ if_pos ha_nonneg ] ; rw [ Real.sq_sqrt <| by nlinarith [ Real.mul_self_sqrt ( show 0 <= Gamma by exact le_of_lt <| Gamma_pos ) ] ] ; rw [ show ( Real.sqrt 2 ) ⁻¹ = Real.sqrt 2 / 2 by rw [ inv_eq_one_div, Real.sqrt_div_self' ] ] ; nlinarith;
  · -- Let x = -a, so 0 ≤ x ≤ √Γ (from ha : -√Γ ≤ a and a < 0). Note a² = x², so √(Γ-a²) = √(Γ-x²) and b0 = √((Γ-x²)/2). Goal reduces, after multiplying by 16, to
    set x := -a
    have hx : 0 ≤ x := by
      exact neg_nonneg_of_nonpos <| le_of_not_ge ha_nonneg
    have hx_le : x ≤ Real.sqrt Gamma := by
      grind
    have hb0 : Real.sqrt ((Gamma - x^2) / 2) = Real.sqrt ((Gamma - a^2) / 2) := by
      grind +splitImp;
    have := negative_analytic ( -a ) hx hx_le;
    unfold Mbound; split_ifs;
    norm_num [ Real.sqrt_div' ] at *;
    field_simp;
    nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, Real.sqrt_nonneg ( Gamma - a ^ 2 ), Real.mul_self_sqrt ( show 0 ≤ Gamma - a ^ 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ Gamma by exact le_of_lt Gamma_pos ) ] ) ]

/-
`a² ≥ Γ`.
-/
lemma case1_arith (n p q cpval : ℕ) (hpq : p + q = n) (hn : 3 ≤ n) (hq : 1 ≤ q)
    (hp : 1 ≤ p) (hcp : cpval ≤ 1 + q * (p - 1))
    (ha2 : Gamma ≤ ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2) :
    (cpval : ℝ) ≤ (1 - Gamma) / 4 * (n : ℝ) ^ 2 := by
      rw [ le_div_iff₀ ( by positivity ) ] at ha2;
      rcases p with ( _ | p ) <;> rcases q with ( _ | q ) <;> norm_num at *;
      rw [ ← hpq ] at * ; norm_num at * ; nlinarith [ ( by norm_cast : ( cpval : ℝ ) ≤ 1 + ( q + 1 ) * p ) ] ;

/-
The `k = 1` sub-case of the `a² < Γ ≤ a² + 2b²` regime. When the maximum clique
`D` of `G[Aᶜ]` has order `1`, `Aᶜ` is independent, so the cruder bound
`cp G ≤ 1 + q·(p-1)` is available, and this already suffices.
-/
lemma case2_k1_arith (n p q k cpval : ℕ) (hpq : p + q = n) (hn : 3 ≤ n) (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hk1 : k = 1) (hcp : cpval ≤ 1 + q * (p - 1))
    (ha2 : ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 < Gamma)
    (hb2 : Gamma ≤ ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 + 2 * ((k : ℝ) / n) ^ 2) :
    (cpval : ℝ) ≤ (1 - Gamma) / 4 * (n : ℝ) ^ 2 := by
      rcases n with ( _ | _ | _ | n ) <;> rcases p with ( _ | _ | p ) <;> rcases q with ( _ | _ | q ) <;> norm_num at *;
      · nlinarith [ show ( cpval : ℝ ) ≤ 1 by norm_cast, show ( Gamma : ℝ ) < 1 / 32 by exact lt_of_lt_of_le ( Gamma_lt ) ( by norm_num ), sq ( n : ℝ ) ];
      · subst_vars; ring_nf at *; norm_num at *;
        nlinarith [ inv_pos.mpr ( by positivity : 0 < ( 9 : ℝ ) + p * 6 + p ^ 2 ), inv_pos.mpr ( by positivity : 0 < ( 3 + p : ℝ ) ^ 2 ), mul_inv_cancel₀ ( by positivity : ( 9 : ℝ ) + p * 6 + p ^ 2 ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 3 + p : ℝ ) ^ 2 ≠ 0 ), Gamma_lt ];
      · subst hk1;
        field_simp at *;
        norm_num [ show n = p + q + 1 by linarith ] at *;
        nlinarith only [ ha2, hb2, show ( cpval : ℝ ) ≤ 1 + ( q + 1 + 1 ) * ( p + 1 ) by norm_cast, Gamma_lt ]

/-
`a² < Γ` and `a² + 2b² ≥ Γ`.
-/
lemma case2_arith (n p q k cpval : ℕ) (hpq : p + q = n) (hn : 3 ≤ n)
    (hp : 1 ≤ p) (hk : k ≤ q) (hk2 : 2 ≤ k)
    (hcp : cpval + Nat.choose k 2 ≤ 2 + q * (p - 1))
    (hb2 : Gamma ≤ ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 + 2 * ((k : ℝ) / n) ^ 2) :
    (cpval : ℝ) ≤ (1 - Gamma) / 4 * (n : ℝ) ^ 2 := by
      rw [ Nat.choose_two_right ] at hcp;
      rw [ ← @Nat.cast_le ℝ ] at * ; norm_num at *;
      rw [ Nat.cast_div ] at * <;> norm_num at *;
      · rw [ Nat.cast_sub, Nat.cast_sub ] at * <;> try linarith;
        field_simp at *;
        norm_num [ show n = p + q by linarith ] at *;
        nlinarith only [ hb2, hcp, show ( k : ℝ ) ≥ 2 by norm_cast, show ( q : ℝ ) ≥ k by norm_cast, show ( p : ℝ ) ≥ 1 by norm_cast, show ( q : ℝ ) ≥ 1 by norm_cast; linarith, Gamma_lt, Gamma_pos, sq_nonneg ( ( p : ℝ ) - q - 2 * k ) ];
      · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )

/-
In the `a² + 2b² < Γ` regime, since `k ≥ 1`, the denominator `n` must be at least `9`
(because `2/n² ≤ 2(k/n)² < Γ < 1/32`).
-/
lemma case3_nn_ge (nn pp qq kk : ℕ) (hnn : 1 ≤ nn) (hk : 1 ≤ kk)
    (hab : ((pp : ℝ) - qq) ^ 2 / (nn : ℝ) ^ 2 + 2 * ((kk : ℝ) / nn) ^ 2 < Gamma) :
    9 ≤ nn := by
      contrapose! hab ; interval_cases nn <;> norm_num at *;
      all_goals nlinarith [ show ( kk : ℝ ) ≥ 1 by norm_cast, Gamma_lt ]

/-
A key gap estimate used in the `a² + 2b² < Γ` regime: in that regime the maximum
clique order `k` of `G[Aᶜ]` is small enough that `p/4 + 3/2 ≤ q - k`.
-/
lemma case3_gap (nn pp qq kk : ℕ) (hpq : pp + qq = nn) (hn9 : 9 ≤ nn) (hk : 1 ≤ kk)
    (hab : ((pp : ℝ) - qq) ^ 2 / (nn : ℝ) ^ 2 + 2 * ((kk : ℝ) / nn) ^ 2 < Gamma) :
    (pp : ℝ) / 4 + 3 / 2 ≤ (qq : ℝ) - kk := by
      rw [ div_add', div_lt_iff₀ ] at hab <;> try positivity;
      nlinarith [ Gamma_lt, show ( nn : ℝ ) ≥ 9 by norm_cast, show ( pp : ℝ ) + qq = nn by norm_cast, show ( kk : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( kk : ℝ ) ( by positivity : ( nn : ℝ ) ≠ 0 ), sq_nonneg ( ( pp : ℝ ) - qq - 2 * kk ), sq_nonneg ( ( pp : ℝ ) - qq + 2 * kk ), mul_le_mul_of_nonneg_left ( show ( kk : ℝ ) ≥ 1 by norm_cast ) ( show ( 0 : ℝ ) ≤ nn by positivity ) ]

/-
`a² + 2b² < Γ`.
-/
lemma case3_arith (n p q k cpval rval : ℕ) (hpq : p + q = n) (hn : 3 ≤ n) (hq : 1 ≤ q)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hkq : k ≤ q)
    (hr : rval ≤ 1 + (q - k) * (k - 1))
    (hcp : (cpval : ℝ) ≤ ((hsplit p q : ℝ) + (p : ℝ) * q + 2 * rval + 1) / 2)
    (ha2 : ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 < Gamma)
    (hab : ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 + 2 * ((k : ℝ) / n) ^ 2 < Gamma) :
    (cpval : ℝ) ≤ (1 - Gamma) / 4 * (n : ℝ) ^ 2 := by
  obtain ⟨pp, qq, kk, nn, rfl, rfl, rfl, rfl⟩ : ∃ pp qq kk nn : ℕ, pp = p ∧ qq = q ∧ kk = k ∧ nn = n := by
    use p, q, k, n;
  obtain ⟨a, b, b0, ha, hb, hb0⟩ : ∃ a b b0 : ℝ, a = (pp - qq : ℝ) / nn ∧ b = (kk : ℝ) / nn ∧ b0 = Real.sqrt ((Gamma - a^2) / 2) ∧ 0 ≤ b ∧ b < b0 ∧ b0 < 1 / 8 ∧ a^2 < Gamma ∧ -Real.sqrt Gamma ≤ a ∧ a ≤ Real.sqrt Gamma := by
    refine' ⟨ _, _, _, rfl, rfl, rfl, _, _, _, _, _ ⟩;
    · positivity;
    · refine' Real.lt_sqrt_of_sq_lt _;
      ring_nf at *; linarith;
    · rw [ Real.sqrt_lt' ] <;> norm_num;
      rw [ div_pow, mul_div, div_add_div, div_lt_iff₀ ] at * <;> norm_num <;> try positivity;
      rw [ sub_div', div_lt_iff₀ ] <;> nlinarith only [ hab, show ( nn : ℝ ) ^ 4 > 0 by positivity, show ( nn : ℝ ) ^ 2 > 0 by positivity, show ( kk : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith only [ hk ], Gamma_lt ];
    · simpa only [ div_pow ] using ha2;
    · constructor <;> nlinarith only [ show 0 ≤ Real.sqrt Gamma by positivity, Real.mul_self_sqrt ( show 0 ≤ Gamma by exact le_of_lt ( by exact Erdos81.Gamma_pos ) ), ha2, show ( pp - qq : ℝ ) ^ 2 / nn ^ 2 ≥ 0 by positivity, show ( pp - qq : ℝ ) ^ 2 / nn ^ 2 = ( ( pp - qq : ℝ ) / nn ) ^ 2 by ring ];
  obtain ⟨beta, hbeta⟩ : ∃ beta : ℝ, beta = qq / nn ∧ beta > 2 / 5 ∧ beta - b > 1 / 4 := by
    have h_beta_b : (qq : ℝ) / nn > 2 / 5 := by
      have h_beta_b : (pp - qq : ℝ)^2 < nn^2 / 25 := by
        rw [ div_lt_iff₀ ] at ha2 <;> nlinarith only [ ha2, show ( nn : ℝ ) ≥ 3 by norm_cast, Gamma_lt ];
      rw [ gt_iff_lt, div_lt_div_iff₀ ] <;> try positivity;
      nlinarith only [ show ( pp : ℝ ) + qq = nn by norm_cast, h_beta_b, show ( nn : ℝ ) ≥ 3 by norm_cast ];
    grind +extAll;
  obtain ⟨hMle, hrfA⟩ : Mbound a b0 ≤ (1 - Gamma) / 4 ∧ (rval : ℝ) ≤ 1 + b0 * (beta - b0) * nn^2 - (beta - b) * nn := by
    apply And.intro;
    · convert quadratic_estimate a _ _ using 1 <;> aesop;
    · have hrf1 : (rval : ℝ) ≤ 1 + (beta - b) * b * nn^2 - (beta - b) * nn := by
        have hrf0 : (rval : ℝ) ≤ 1 + (qq - kk) * (kk - 1) := by
          norm_cast;
        convert hrf0 using 1 ; push_cast [ hb, hbeta ] ; ring_nf;
        simp +decide [ show nn ≠ 0 by linarith ];
      have hle : b * (beta - b) ≤ b0 * (beta - b0) := by
        nlinarith only [ hb0, hbeta, mul_le_mul_of_nonneg_left hb0.2.2.1.le hb0.2.1 ];
      nlinarith [ hrf1, mul_le_mul_of_nonneg_right hle (sq_nonneg (nn : ℝ)) ];
  have hnn0 : (nn : ℝ) ≠ 0 := by positivity
  by_cases hq_le_pp : qq ≤ pp;
  · obtain ⟨hMeq, hcp2⟩ : Mbound a b0 * nn^2 = 1 / 2 * (pp^2 / 2 + pp * qq + 2 * b0 * (beta - b0) * nn^2) ∧ (cpval : ℝ) ≤ (pp^2 / 2 + pp / 2 + pp * qq + 2 * rval + 1) / 2 := by
      constructor;
      · unfold Mbound;
        rw [ if_pos ];
        · rw [ ha, hbeta.1 ] ; ring_nf;
          field_simp;
          rw [ show ( nn : ℝ ) = pp + qq by norm_cast; linarith ] ; ring;
        · exact ha.symm ▸ div_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr hq_le_pp ) ) ( Nat.cast_nonneg _ );
      · convert hcp using 1;
        rw [ hsplit_eq_ge hq_le_pp ];
    have hbk : (beta - b) * nn = (qq : ℝ) - kk := by rw [ hbeta.1, hb ] ; field_simp
    have hn9 : 9 ≤ nn := case3_nn_ge nn pp qq kk (by omega) hk hab
    have hgap : (pp : ℝ) / 4 + 3 / 2 ≤ (qq : ℝ) - kk := case3_gap nn pp qq kk hpq hn9 hk hab
    nlinarith [ hgap, hbk, hrfA, hcp2, hMeq, mul_le_mul_of_nonneg_right hMle (show (0:ℝ) ≤ (nn:ℝ)^2 by positivity) ];
  · have hsplit_val : (hsplit pp qq : ℝ) = pp * qq - pp^2 / 2 + pp / 2 := by
      convert hsplit_eq_lt ( show pp < qq from lt_of_not_ge hq_le_pp ) using 1;
    have hMeq : Mbound a b0 * nn^2 = (pp * qq - pp^2 / 2 + pp * qq + 2 * b0 * (beta - b0) * nn^2) / 2 := by
      unfold Mbound; split_ifs <;> simp_all +decide ;
      · exact False.elim <| absurd ‹0 ≤ ( pp - qq : ℝ ) / nn› <| not_le_of_gt <| div_neg_of_neg_of_pos ( sub_neg_of_lt <| Nat.cast_lt.mpr hq_le_pp ) <| by positivity;
      · field_simp;
        rw [ show ( nn : ℝ ) = pp + qq by norm_cast; linarith ] ; ring;
    have hbk : (beta - b) * nn = (qq : ℝ) - kk := by rw [ hbeta.1, hb ] ; field_simp
    have hn9 : 9 ≤ nn := case3_nn_ge nn pp qq kk (by omega) hk hab
    have hgap : (pp : ℝ) / 4 + 3 / 2 ≤ (qq : ℝ) - kk := case3_gap nn pp qq kk hpq hn9 hk hab
    nlinarith [ hgap, hbk, hrfA, hcp, hsplit_val, hMeq, mul_le_mul_of_nonneg_right hMle (show (0:ℝ) ≤ (nn:ℝ)^2 by positivity) ]

/-
**Theorem (Explicit upper bound for Erdős Problem #81).**
Every chordal graph on `n ≥ 3` vertices `G` satisfies
`cp G ≤ (1/4 - c₀) n²`, with `c₀ ≥ 1/133`.
-/
theorem erdos81 (G : SimpleGraph V) (hG : IsChordal G) (hn : 3 ≤ Fintype.card V) :
    (cp G : ℝ) ≤ (1 / 4 - c0) * (Fintype.card V : ℝ) ^ 2 ∧ (1 : ℝ) / 133 ≤ c0 := by
  refine ⟨?_, c0_ge⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset V, IsMaxClique G A := exists_maxClique G
  set p := A.card
  set C := Aᶜ
  set q := C.card
  set n := Fintype.card V
  have hpq : p + q = n := by
    exact Finset.card_add_card_compl A
  have hp : 1 ≤ p := by
    exact Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by rintro rfl; exact absurd ( hA.2 { Classical.choose ( Finset.card_pos.mp ( pos_of_gt hn ) ) } ( by simp +decide ) ) ( by aesop ) ) )
  by_cases hq : q = 0
  generalize_proofs at *;
  · -- Since $q = 0$, we have $C = \emptyset$, so $eBetween G A \emptyset = 0$ and $eIn G \emptyset = 0$, and $cp_le_A_singles$ gives $cp G \leq 1$.
    have hcp_le_one : (cp G : ℝ) ≤ 1 := by
      convert cp_le_A_singles G A hA using 1
      generalize_proofs at *;
      rw [ show Aᶜ = ∅ by exact Finset.card_eq_zero.mp hq ] ; simp +decide [ eBetween, eIn ] ; norm_cast;
    rw [ show c0 = Gamma / 4 by rfl ] ; nlinarith [ show ( n : ℝ ) ≥ 3 by norm_cast, show ( Gamma : ℝ ) < 1 / 32 by exact_mod_cast Gamma_lt ] ;
  · have := exists_maxClique_on G C ( Finset.card_pos.mp ( Nat.pos_of_ne_zero hq ) ) ; obtain ⟨ D, hDsub, hDcl, hDmax, hk ⟩ := this; set k := D.card;
    obtain ⟨ R, hR₁, hR₂, hR₃ ⟩ := relative_partition G hG C D hDsub hDcl hDmax hk;
    by_cases ha2 : Gamma ≤ ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2;
    · convert case1_arith n p q ( cp G ) hpq hn ( Nat.pos_of_ne_zero hq ) hp _ ha2 using 1;
      · unfold c0; ring;
      · exact le_trans ( cp_le_A_singles G A hA ) ( by linarith [ edges_outside G hG A hA ] );
    · by_cases hb2 : Gamma ≤ ((p : ℝ) - q) ^ 2 / (n : ℝ) ^ 2 + 2 * ((k : ℝ) / n) ^ 2;
      · by_cases hk1 : k = 1;
        · convert case2_k1_arith n p q k ( cp G ) hpq hn hp ( Nat.pos_of_ne_zero hq ) hk1 _ ( not_le.mp ha2 ) hb2 using 1;
          · unfold c0; ring;
          · exact le_trans ( cp_le_A_singles G A hA ) ( by linarith [ edges_outside G hG A hA ] );
        · have hk2 : 2 ≤ k := by omega;
          have hp2 : 2 ≤ p := by
            contrapose! ha2;
            interval_cases p ; norm_num at *;
            refine' le_trans _ ( show ( 1 - q : ℝ ) ^ 2 / n ^ 2 ≥ 1 / 9 by rw [ ge_iff_le, div_le_div_iff₀ ] <;> nlinarith only [ show ( n : ℝ ) ≥ 3 by norm_cast, sq_nonneg ( ( n : ℝ ) - 3 ), show ( q : ℝ ) = n - 1 by exact eq_sub_of_add_eq' ( mod_cast hpq ) ] );
            exact le_trans ( le_of_lt ( Gamma_lt ) ) ( by norm_num );
          convert case2_arith n p q k ( cp G ) hpq hn hp ( show k ≤ q from Finset.card_le_card hDsub ) hk2 _ hb2 using 1;
          · unfold c0; ring;
          · have := cp_le_A_cross_R G A hA.1 hp2 R hR₁;
            have := edges_outside G hG A hA;
            grind;
      · have hcp : (cp G : ℝ) ≤ (hsplit p q + p * q + 2 * R.card + 1) / 2 := by
          have hcp : (cp G : ℝ) ≤ 1 + eBetween G A C + R.card := by
            have := cp_le_A_cross_R G A ( hA.1 ) ( by
              contrapose! ha2; interval_cases _ : A.card ; simp_all +decide ;
              · aesop;
              · simp +zetaDelta at *;
                simp_all +decide [ Finset.card_compl ];
                rw [ Nat.cast_sub ( by linarith ) ] ; norm_num;
                rw [ le_div_iff₀ ] <;> nlinarith only [ show ( Fintype.card V : ℝ ) ≥ 3 by norm_cast, sq_nonneg ( ( Fintype.card V : ℝ ) - 3 ), Gamma_lt ] ) R hR₁; norm_cast;
          have hcp : (cp G : ℝ) ≤ hsplit p q + (p * q - eBetween G A C) + R.card := by
            convert cp_le_split G A hA.1 R hR₁ using 1;
            rw [ ← @Nat.cast_le ℝ ] ; norm_num;
            rw [ Nat.cast_sub ] <;> norm_num;
            · norm_cast;
            · exact le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide [ Finset.card_product ] );
          linarith;
        convert case3_arith n p q k ( cp G ) R.card hpq hn ( Nat.pos_of_ne_zero hq ) hp hk ( Finset.card_le_card hDsub ) hR₃ hcp ( not_le.mp ha2 ) ( not_le.mp hb2 ) using 1;
        unfold c0; ring;

#print axioms erdos81

end Erdos81

end
