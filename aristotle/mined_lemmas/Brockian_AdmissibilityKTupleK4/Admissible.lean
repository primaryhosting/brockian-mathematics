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

def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- If a prime `p` exceeds the size of `H`, then `H` automatically misses a residue class
modulo `p`. -/
