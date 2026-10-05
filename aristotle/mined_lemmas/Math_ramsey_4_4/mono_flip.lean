/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4

We show that the two-colour Ramsey number `R(4,4)` equals `18`:

* every symmetric two-colouring of the edges of the complete graph on `18` vertices
  contains a monochromatic set of `4` vertices;
* there is a symmetric two-colouring of the edges of the complete graph on `17` vertices
  (the Paley graph of order `17`) with no monochromatic set of `4` vertices.
-/

namespace Math

open Finset

/-- `MonoSet f b S` says that every pair of distinct vertices of `S` receives colour `b`. -/

lemma mono_flip {b : Bool} {S : Finset V} :
    MonoSet (fun i j => !f i j) b S ↔ MonoSet f (!b) S := by
  have key : ∀ x y : Bool, ((!x) = y) ↔ (x = !y) := by decide
  constructor <;> intro h i hi j hj hij
  · exact (key _ _).mp (h i hi j hj hij)
  · exact (key _ _).mpr (h i hi j hj hij)

/-- Handshake lemma: the sum over `W` of the number of `true`-neighbours in `W` is even. -/
