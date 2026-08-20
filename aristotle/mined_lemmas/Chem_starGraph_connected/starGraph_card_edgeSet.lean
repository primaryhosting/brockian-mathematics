import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open SimpleGraph

/-! ### Star graphs are trees

We need a supply of concrete finite trees in order to exhibit examples of the
structure defined below; the simplest such family is the star graph. -/

/-- The star graph on `V` centred at `c`: `a` and `b` are adjacent iff they are
distinct and one of them is the centre `c`. -/

lemma starGraph_card_edgeSet {V : Type*} [Finite V] (c : V) :
    Nat.card (starGraph c).edgeSet + 1 = Nat.card V := by
  classical
  have : Fintype V := Fintype.ofFinite V
  haveI : Nonempty V := ⟨c⟩
  have h1 : Nat.card (starGraph c).edgeSet = Nat.card {v : V // v ≠ c} :=
    (Nat.card_eq_of_bijective _ (starGraph_edge_bijective c)).symm
  have h2 : Fintype.card {v : V // ¬ (v = c)} = Fintype.card V - Fintype.card {v : V // v = c} :=
    Fintype.card_subtype_compl _
  have h3 : Fintype.card {v : V // v = c} = 1 := Fintype.card_subtype_eq c
  have h4 : 0 < Fintype.card V := Fintype.card_pos
  rw [h1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [ne_eq]
  omega

