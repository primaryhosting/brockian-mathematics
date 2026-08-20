/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`, i.e. some residue class mod `p` is missed. -/

theorem isAdmissible_zero_two_six_eight :
    IsAdmissible ({0, 2, 6, 8} : Finset ℤ) := by
  apply AdmissibilityKTupleK4
  · decide
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide
  · refine ⟨1, ?_⟩
    intro h hh
    fin_cases hh <;> decide

end Brockian

