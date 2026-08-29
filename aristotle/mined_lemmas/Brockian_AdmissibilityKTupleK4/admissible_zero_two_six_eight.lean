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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` (thought of as a tuple of shifts `h₁ < ⋯ < h_k`) is
*admissible* if for every prime `p` the elements of `H` do not cover all residue classes
modulo `p`; equivalently, some residue class mod `p` is missed by `H`.  This is the
classical admissibility condition from the Hardy–Littlewood prime `k`-tuple conjecture. -/

theorem admissible_zero_two_six_eight : Admissible ({0, 2, 6, 8} : Finset ℤ) := by
  have hcard : ({0, 2, 6, 8} : Finset ℤ).card = 4 := by decide
  rw [AdmissibilityKTupleK4 _ hcard]
  constructor
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩

/-- Tuple form of the criterion: for an injective `4`-tuple `h : Fin 4 → ℤ`, admissibility of
its range is equivalent to missing a residue class modulo `2` and modulo `3`. -/
