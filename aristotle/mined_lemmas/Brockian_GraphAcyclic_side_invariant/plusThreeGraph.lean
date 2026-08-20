import Mathlib
namespace Brockian.GraphAcyclic

/-- Twin-admissible residue: both a and a+2 are units mod n. -/

def plusThreeGraph (n : ℕ) : SimpleGraph (ZMod n) where
  Adj a b := (b - a = 3 ∨ a - b = 3) ∧ a ≠ b
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

section Height

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- If `g` is an injective "height" function whose values change by exactly one along every edge
of `H`, then, given `a b` with `g b = g a + 1`, a walk of `H` avoiding the edge `s(a, b)` cannot
cross the level `g a`. -/
