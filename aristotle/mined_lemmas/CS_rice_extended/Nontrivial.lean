/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Classical

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- The index set of a property `P` of partial functions: the set of (codes of) programs
whose computed partial function has the property `P`. -/

def Nontrivial (P : Set (ℕ →. ℕ)) : Prop :=
  (∃ f, Nat.Partrec f ∧ f ∈ P) ∧ (∃ g, Nat.Partrec g ∧ g ∉ P)

/-- **Rice's theorem (extended form).**  If `P` is a nontrivial property of partial
functions — i.e. it is satisfied by some partial recursive function and refuted by some
other partial recursive function — then its index set `{c | eval c ∈ P}` is not
recursive.  Since membership only depends on the *function computed* by the code, this
covers every nontrivial semantic property of programs. -/
