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

def indexSet (P : Set (ℕ →. ℕ)) : Set Nat.Partrec.Code :=
  {c | Nat.Partrec.Code.eval c ∈ P}

/-- The index set of `P`, transported to natural-number indices via the standard
enumeration of codes. -/
