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

lemma starGraph_edge_bijective {V : Type*} (c : V) :
    Function.Bijective (fun v : {v : V // v ≠ c} =>
      (⟨s(c, v.1), by
        have : (starGraph c).Adj c v.1 := ⟨fun h => v.2 h.symm, Or.inl rfl⟩
        simpa using this⟩ : (starGraph c).edgeSet)) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq, Sym2.congr_right] at hab
    exact Subtype.ext hab
  · rintro ⟨e, he⟩
    induction e with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨hab, h⟩ := he
      rcases h with h | h
      · subst h
        exact ⟨⟨b, fun hb => hab hb.symm⟩, rfl⟩
      · subst h
        exact ⟨⟨a, hab⟩, Subtype.ext (Sym2.eq_swap)⟩

