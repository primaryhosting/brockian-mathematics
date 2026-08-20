/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* of a shift pattern `H` at modulus `n`: the number of residues
`a : ZMod n` for which none of the shifted values `a + h`, `h ∈ H`, vanishes modulo `n`.
For a prime `n = p` this is the quantity `ν_H(p)` occurring in the singular series of the
Hardy–Littlewood prime constellation conjecture. -/

def localCount (H : Finset ℤ) (n : ℕ) [NeZero n] : ℕ :=
  ((Finset.univ : Finset (ZMod n)).filter fun a => ∀ h ∈ H, a + (h : ZMod n) ≠ 0).card

/-- The admissible residues are exactly the complement of the set of forbidden residues
`{-h : h ∈ H}`. -/
