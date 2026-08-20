import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/
noncomputable def nbrs (s : Finset V) (G : SimpleGraph V) (v : V) : Finset V :=
  (s.erase v).filter (fun x => G.Adj v x)

lemma mem_nbrs {s : Finset V} {G : SimpleGraph V} {v x : V} :
    x ∈ nbrs s G v ↔ (x ∈ s ∧ x ≠ v ∧ G.Adj v x) := by
  simp [nbrs, Finset.mem_filter, Finset.mem_erase, and_assoc]
  tauto

lemma nbrs_subset (s : Finset V) (G : SimpleGraph V) (v : V) : nbrs s G v ⊆ s.erase v :=
  Finset.filter_subset _ _

/-- Identify the vertex `w` with the vertex `u`: every neighbour of `w` becomes a neighbour
of `u`.  (Used with `u` and `w` two non-adjacent neighbours of a degree-5 vertex, in which
case this is precisely the contraction of the two edges `vu` and `vw`.) -/
def contract (G : SimpleGraph V) (u w : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ (a = u ∧ G.Adj w b) ∨ (b = u ∧ G.Adj w a))
  symm := by
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  loopless := by constructor; rintro a ⟨hne, -⟩; exact hne rfl

/-- The reduction relation: `Reduces s G t H` says that the graph `H` on the vertex set `t`
can be obtained from the graph `G` on the vertex set `s` by repeatedly deleting a vertex, or
contracting a degree-`≤ 5` vertex `v` into two of its non-adjacent neighbours `u`, `w`.
Both operations preserve planarity. -/
inductive Reduces : Finset V → SimpleGraph V → Finset V → SimpleGraph V → Prop
  | refl (s : Finset V) (G : SimpleGraph V) : Reduces s G s G
  | del {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V} (v : V) :
      Reduces (s.erase v) G t H → Reduces s G t H
  | con {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V} (v u w : V)
      (hu : u ∈ nbrs s G v) (hw : w ∈ nbrs s G v) (huw : u ≠ w) (hnadj : ¬ G.Adj u w) :
      Reduces ((s.erase v).erase w) (contract G u w) t H → Reduces s G t H

/-- The local degree condition that Euler's formula (together with the non-planarity of `K₅`)
provides for a planar graph: there is a vertex of degree at most `4`, or a vertex of degree at
most `5` two of whose neighbours are non-adjacent. -/
def LowDegreeVertex (s : Finset V) (G : SimpleGraph V) : Prop :=
  s.Nonempty → ∃ v ∈ s, (nbrs s G v).card ≤ 4 ∨
    ((nbrs s G v).card ≤ 5 ∧ ∃ u ∈ nbrs s G v, ∃ w ∈ nbrs s G v, u ≠ w ∧ ¬ G.Adj u w)

/-- The combinatorial hypothesis extracted from planarity: every graph reachable from `(s, G)`
by vertex deletions and contractions has a low degree vertex in the above sense.

Every planar graph satisfies this: planarity is preserved by vertex deletion and by edge
contraction, Euler's formula gives a vertex `v` of degree at most `5` in any planar graph, and
if `v` has degree exactly `5` then two of its neighbours must be non-adjacent, since otherwise
`K₆` (hence `K₅`) would be a subgraph. -/
def FiveColorReducible (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ (t : Finset V) (H : SimpleGraph V), Reduces s G t H → LowDegreeVertex t H

/-- A proper `5`-colouring of the graph `G` restricted to the vertex set `s`. -/
def IsProperColoring (s : Finset V) (G : SimpleGraph V) (c : V → Fin 5) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → c x ≠ c y

/-- `G` restricted to the vertex set `s` is `5`-colourable. -/
def FiveColorable (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 5, IsProperColoring s G c

omit [DecidableEq V] in
lemma exists_free_color (T : Finset V) (g : V → Fin 5) (hT : T.card ≤ 4) :
    ∃ f : Fin 5, ∀ y ∈ T, g y ≠ f := by
  have h1 : (T.image g).card ≤ 4 := le_trans Finset.card_image_le hT
  have : ∃ f : Fin 5, f ∉ T.image g := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin 5)) ⊆ T.image g := fun x _ => hcon x
    have := Finset.card_le_card this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨f, hf⟩ := this
  exact ⟨f, fun y hy hgy => hf (Finset.mem_image.2 ⟨y, hy, hgy⟩)⟩

/-- The heart of the five colour theorem: a graph satisfying the reduction hypothesis coming
from planarity is `5`-colourable.  The proof is by induction on the number of vertices, using
the classical contraction argument of Kempe/Wernicke. -/
theorem fiveColorable_of_reducible :
    ∀ (n : ℕ) (s : Finset V) (G : SimpleGraph V), s.card ≤ n → FiveColorReducible s G →
      FiveColorable s G := by
  intro n
  induction n with
  | zero =>
      intro s G hs _
      have : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
      subst this
      exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
  | succ n ih =>
      intro s G hs hgood
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
      obtain ⟨v, hv, hcase⟩ := hgood s G (Reduces.refl s G) hne
      rcases hcase with hdeg | ⟨hdeg, u, hu, w, hw, huw, hnadj⟩
      · -- Case A: `v` has at most four neighbours; delete it.
        have hcard : (s.erase v).card ≤ n := by
          have := Finset.card_erase_of_mem hv
          omega
        have hgood' : FiveColorReducible (s.erase v) G := by
          intro t H hred
          exact hgood t H (Reduces.del v hred)
        obtain ⟨c', hc'⟩ := ih (s.erase v) G hcard hgood'
        obtain ⟨f, hf⟩ := exists_free_color (nbrs s G v) c' hdeg
        refine ⟨Function.update c' v f, ?_⟩
        intro x hx y hy hadj
        by_cases hxv : x = v
        · subst hxv
          have hyx : y ≠ x := (hadj.ne).symm
          have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
          simp only [Function.update_apply, if_neg hyx]
          exact fun h => hf y hy' h.symm
        · by_cases hyv : y = v
          · subst hyv
            have hxy : x ≠ y := hadj.ne
            have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
            simp only [Function.update_apply, if_neg hxy]
            exact fun h => hf x hx' h
          · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
            exact hc' x (Finset.mem_erase.2 ⟨hxv, hx⟩) y (Finset.mem_erase.2 ⟨hyv, hy⟩) hadj
      · -- Case B: `v` has five neighbours, two of which, `u` and `w`, are non-adjacent.
        obtain ⟨hus, huv, hadjvu⟩ := mem_nbrs.1 hu
        obtain ⟨hws, hwv, hadjvw⟩ := mem_nbrs.1 hw
        set s' : Finset V := (s.erase v).erase w with hs'
        set G' : SimpleGraph V := contract G u w with hG'
        have hcard : s'.card ≤ n := by
          have h1 := Finset.card_erase_of_mem hv
          have h2 : s'.card ≤ (s.erase v).card := Finset.card_erase_le
          omega
        have hgood' : FiveColorReducible s' G' := by
          intro t H hred
          exact hgood t H (Reduces.con v u w hu hw huw hnadj hred)
        obtain ⟨c', hc'⟩ := ih s' G' hcard hgood'
        -- first give `w` the colour of `u`
        set c₀ : V → Fin 5 := Function.update c' w (c' u) with hc₀
        have hc₀u : c₀ u = c' u := by simp [hc₀, huw]
        have hc₀w : c₀ w = c' u := by simp [hc₀]
        have hc₀other : ∀ x, x ≠ w → c₀ x = c' x := by
          intro x hx; simp [hc₀, hx]
        have hus' : u ∈ s' := by
          simp only [hs', Finset.mem_erase]
          exact ⟨huw, huv, hus⟩
        -- the colours used on the neighbourhood of `v` : at most four of them
        have hsub : ((nbrs s G v).erase w).card ≤ 4 := by
          have := Finset.card_erase_of_mem hw
          omega
        obtain ⟨f, hf⟩ := exists_free_color ((nbrs s G v).erase w) c₀ hsub
        have hfree : ∀ y ∈ nbrs s G v, c₀ y ≠ f := by
          intro y hy
          by_cases hyw : y = w
          · subst hyw
            rw [hc₀w, ← hc₀u]
            exact hf u (Finset.mem_erase.2 ⟨huw, hu⟩)
          · exact hf y (Finset.mem_erase.2 ⟨hyw, hy⟩)
        refine ⟨Function.update c₀ v f, ?_⟩
        have key : ∀ x ∈ s, ∀ y ∈ s, x ≠ v → y ≠ v → G.Adj x y → c₀ x ≠ c₀ y := by
          intro x hx y hy hxv hyv hadj
          by_cases hxw : x = w
          · subst hxw
            have hyx : y ≠ x := (hadj.ne).symm
            have hyu : y ≠ u := by
              rintro rfl
              exact hnadj (hadj.symm)
            have hy' : y ∈ s' := by
              simp only [hs', Finset.mem_erase]
              exact ⟨hyx, hyv, hy⟩
            have hadj' : G'.Adj u y := by
              refine ⟨Ne.symm hyu, ?_⟩
              right; left; exact ⟨rfl, hadj⟩
            rw [hc₀w, hc₀other y hyx]
            exact hc' u hus' y hy' hadj'
          · by_cases hyw : y = w
            · subst hyw
              have hxy : x ≠ y := hadj.ne
              have hxu : x ≠ u := by
                rintro rfl
                exact hnadj hadj
              have hx' : x ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hxy, hxv, hx⟩
              have hadj' : G'.Adj x u := by
                refine ⟨hxu, ?_⟩
                right; right; exact ⟨rfl, hadj.symm⟩
              rw [hc₀w, hc₀other x hxy]
              exact hc' x hx' u hus' hadj'
            · have hx' : x ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hxw, hxv, hx⟩
              have hy' : y ∈ s' := by
                simp only [hs', Finset.mem_erase]
                exact ⟨hyw, hyv, hy⟩
              have hadj' : G'.Adj x y := ⟨hadj.ne, Or.inl hadj⟩
              rw [hc₀other x hxw, hc₀other y hyw]
              exact hc' x hx' y hy' hadj'
        intro x hx y hy hadj
        by_cases hxv : x = v
        · subst hxv
          have hyx : y ≠ x := (hadj.ne).symm
          have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
          simp only [Function.update_apply, if_neg hyx]
          exact fun h => hfree y hy' h.symm
        · by_cases hyv : y = v
          · subst hyv
            have hxy : x ≠ y := hadj.ne
            have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
            simp only [Function.update_apply, if_neg hxy]
            exact fun h => hfree x hx' h
          · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
            exact key x hx y hy hxv hyv hadj

/-- **Five Colour Theorem** (combinatorial core).  Every finite graph satisfying the
planarity-derived reduction hypothesis `FiveColorReducible` is `5`-colourable. -/
theorem five_color_theorem_of_reducible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h : FiveColorReducible (Finset.univ : Finset V) G) : G.Colorable 5 := by
  obtain ⟨c, hc⟩ := fiveColorable_of_reducible (Fintype.card V) Finset.univ G
    (le_of_eq (Finset.card_univ)) h
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro a b hab
  exact hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab

/-- The vertex set `s` carries no `K₆`: among any six of its vertices, two are non-adjacent.
A planar graph has this property, since `K₆` contains `K₅`, which is not planar. -/
def NoK6 (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ K : Finset V, K ⊆ s → K.card = 6 → ∃ x ∈ K, ∃ y ∈ K, x ≠ y ∧ ¬ G.Adj x y

/-- A vertex of degree at most `5` (which Euler's formula provides for planar graphs)
together with the absence of a `K₆` gives the local condition `LowDegreeVertex`. -/
lemma lowDegreeVertex_of_minDegree_le_five {s : Finset V} {G : SimpleGraph V}
    (hmin : s.Nonempty → ∃ v ∈ s, (nbrs s G v).card ≤ 5) (h6 : NoK6 s G) :
    LowDegreeVertex s G := by
  intro hne
  obtain ⟨v, hv, hdeg⟩ := hmin hne
  rcases le_or_gt (nbrs s G v).card 4 with h | h
  · exact ⟨v, hv, Or.inl h⟩
  refine ⟨v, hv, Or.inr ⟨hdeg, ?_⟩⟩
  by_contra hcon
  push_neg at hcon
  have hvnot : v ∉ nbrs s G v := by simp [mem_nbrs]
  have hKcard : (insert v (nbrs s G v)).card = 6 := by
    rw [Finset.card_insert_of_notMem hvnot]; omega
  have hKsub : insert v (nbrs s G v) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hv
    · exact (mem_nbrs.1 hx).1
  obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := h6 _ hKsub hKcard
  rcases Finset.mem_insert.1 hx with rfl | hx'
  · exact hnadj (mem_nbrs.1 (by simpa [hxy.symm] using hy)).2.2
  · rcases Finset.mem_insert.1 hy with rfl | hy'
    · exact hnadj ((mem_nbrs.1 hx').2.2).symm
    · exact hnadj (hcon x hx' y hy' hxy)

/-- **Five Colour Theorem** (combinatorial core, in terms of degrees and `K₆`).

Let `G` be a finite simple graph with the property that every graph obtained from `G` by
repeatedly deleting vertices and contracting a vertex into two of its non-adjacent neighbours
(both operations preserve planarity) has a vertex of degree at most `5` and contains no `K₆`.
Then `G` is `5`-colourable.

For a planar graph the first hypothesis is exactly the consequence of Euler's formula
(`|E| ≤ 3|V| - 6`, hence a vertex of degree at most `5`) and the second holds because `K₆`
contains the non-planar graph `K₅`.  Deriving these two facts from a formal definition of
planarity is not carried out here; the present statement isolates the combinatorial heart of
the theorem, the Kempe/Wernicke contraction argument. -/
theorem five_color_theorem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ (t : Finset V) (H : SimpleGraph V), Reduces Finset.univ G t H →
      t.Nonempty → ∃ v ∈ t, (nbrs t H v).card ≤ 5)
    (hK6 : ∀ (t : Finset V) (H : SimpleGraph V), Reduces Finset.univ G t H → NoK6 t H) :
    G.Colorable 5 :=
  five_color_theorem_of_reducible G fun t H hred =>
    lowDegreeVertex_of_minDegree_le_five (hdeg t H hred) (hK6 t H hred)

/-- Reductions only shrink the vertex set. -/
lemma Reduces.subset {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V}
    (h : Reduces s G t H) : t ⊆ s := by
  induction h with
  | refl s G => exact Finset.Subset.refl s
  | del v _ ih => exact ih.trans (Finset.erase_subset _ _)
  | con v u w hu hw huw hnadj _ ih =>
      exact ih.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))

/-- The base case of the five colour theorem: a graph on at most five vertices satisfies the
reduction hypothesis (all degrees stay at most `4`). -/
theorem fiveColorReducible_of_card_le_five (s : Finset V) (G : SimpleGraph V) (hs : s.card ≤ 5) :
    FiveColorReducible s G := by
  intro t H hred hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, hv, Or.inl ?_⟩
  have h1 := Finset.card_le_card (nbrs_subset t H v)
  have h2 : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hv
  have h3 : t.card ≤ 5 := le_trans (Finset.card_le_card hred.subset) hs
  have h4 : 1 ≤ t.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

/-- The base case of the five colour theorem: every graph on at most five vertices is
`5`-colourable. -/
theorem five_color_theorem_card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 5) : G.Colorable 5 :=
  five_color_theorem_of_reducible G
    (fiveColorReducible_of_card_le_five Finset.univ G (by simpa using hV))

/-- `G` is `4`-degenerate on `s`: every nonempty subset of `s` contains a vertex having at
most four neighbours inside that subset. -/
def FourDegenerate (s : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ t ⊆ s, t.Nonempty → ∃ v ∈ t, (nbrs t G v).card ≤ 4

/-- The greedy half of the five colour theorem: a `4`-degenerate graph is `5`-colourable. -/
theorem fiveColorable_of_fourDegenerate :
    ∀ (n : ℕ) (s : Finset V) (G : SimpleGraph V), s.card ≤ n → FourDegenerate s G →
      FiveColorable s G := by
  intro n
  induction n with
  | zero =>
      intro s G hs _
      have : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
      subst this
      exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
  | succ n ih =>
      intro s G hs hdeg
      rcases Finset.eq_empty_or_nonempty s with rfl | hne
      · exact ⟨fun _ => 0, by simp [IsProperColoring]⟩
      obtain ⟨v, hv, hd⟩ := hdeg s (Finset.Subset.refl s) hne
      have hcard : (s.erase v).card ≤ n := by
        have := Finset.card_erase_of_mem hv
        omega
      have hdeg' : FourDegenerate (s.erase v) G := fun t ht =>
        hdeg t (ht.trans (Finset.erase_subset _ _))
      obtain ⟨c', hc'⟩ := ih (s.erase v) G hcard hdeg'
      obtain ⟨f, hf⟩ := exists_free_color (nbrs s G v) c' hd
      refine ⟨Function.update c' v f, ?_⟩
      intro x hx y hy hadj
      by_cases hxv : x = v
      · subst hxv
        have hyx : y ≠ x := (hadj.ne).symm
        have hy' : y ∈ nbrs s G x := mem_nbrs.2 ⟨hy, hyx, hadj⟩
        simp only [Function.update_apply, if_neg hyx]
        exact fun h => hf y hy' h.symm
      · by_cases hyv : y = v
        · subst hyv
          have hxy : x ≠ y := hadj.ne
          have hx' : x ∈ nbrs s G y := mem_nbrs.2 ⟨hx, hxy, hadj.symm⟩
          simp only [Function.update_apply, if_neg hxy]
          exact fun h => hf x hx' h
        · simp only [Function.update_apply, if_neg hxv, if_neg hyv]
          exact hc' x (Finset.mem_erase.2 ⟨hxv, hx⟩) y (Finset.mem_erase.2 ⟨hyv, hy⟩) hadj

/-- Every `4`-degenerate finite graph is `5`-colourable. -/
theorem five_color_theorem_of_fourDegenerate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : FourDegenerate (Finset.univ : Finset V) G) : G.Colorable 5 := by
  obtain ⟨c, hc⟩ := fiveColorable_of_fourDegenerate (Fintype.card V) Finset.univ G
    (le_of_eq Finset.card_univ) h
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro a b hab
  exact hc a (Finset.mem_univ a) b (Finset.mem_univ b) hab

end Frontier

