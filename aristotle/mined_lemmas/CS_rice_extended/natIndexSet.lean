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

def natIndexSet (P : Set (ℕ →. ℕ)) : Set ℕ :=
  {n | Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) ∈ P}

/-- A property of partial functions is *nontrivial* (as a semantic property of programs)
if some partial recursive function has it and some partial recursive function fails it. -/
