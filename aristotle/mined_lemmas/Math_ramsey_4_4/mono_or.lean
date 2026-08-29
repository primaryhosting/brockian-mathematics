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

lemma mono_or {b : Bool} {S : Finset V} (h : MonoSet f b S) :
    MonoSet f true S ∨ MonoSet f false S := by
  cases b
  · exact Or.inr h
  · exact Or.inl h

omit [DecidableEq V] in
