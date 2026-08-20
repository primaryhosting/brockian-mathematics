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

def starGraph {V : Type*} (c : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (a = c ∨ b = c)
  symm := by
    rintro a b ⟨hab, h⟩
    exact ⟨hab.symm, h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma starGraph_connected {V : Type*} [Nonempty V] (c : V) : (starGraph c).Connected := by
  have key : ∀ x : V, (starGraph c).Reachable x c := by
    intro x
    by_cases hx : x = c
    · subst hx; rfl
    · exact SimpleGraph.Adj.reachable (G := starGraph c) ⟨hx, Or.inr rfl⟩
  exact { preconnected := fun a b => (key a).trans (key b).symm }

/-- The edges of the star graph centred at `c` are exactly the pairs `s(c, v)`
with `v ≠ c`. -/
