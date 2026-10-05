import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

open scoped Classical

/-- A property `C` of programs (codes) is *semantic* (extensional) if it depends only on the
partial function the program computes. -/

def Nontrivial (C : Set Code) : Prop :=
  (∃ c, c ∈ C) ∧ ∃ c, c ∉ C

/-- If membership in a set of codes is decidable by a computable procedure, then the "flip"
function, sending codes in `C` to a fixed code `a` and codes outside `C` to a fixed code `b`,
is computable. -/
