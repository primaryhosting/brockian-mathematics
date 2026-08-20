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

theorem rice_extended (P : Set (ℕ →. ℕ)) (hP : Nontrivial P) :
    ¬ ComputablePred (fun c : Nat.Partrec.Code => c ∈ indexSet P) := by
  rintro h
  obtain ⟨⟨f, hfp, hfP⟩, ⟨g, hgp, hgP⟩⟩ := hP
  exact hgP (ComputablePred.rice P h hfp hgp hfP)

/-- The same statement phrased for natural-number indices: the set of natural numbers
coding programs with a nontrivial semantic property is not recursive. -/
