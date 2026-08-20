/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

/-- The local count of a constellation (`k`-tuple of shifts) `H` modulo `p`:
the number of residues `n` mod `p` such that none of the shifted values
`n + H i` is divisible by `p`. -/

noncomputable def localCount {p : ℕ} [NeZero p] {k : ℕ} (H : Fin k → ZMod p) : ℕ :=
  (Finset.univ.filter fun n : ZMod p => ∀ i : Fin k, n + H i ≠ 0).card

/-- The excluded residues are exactly the negatives of the shifts. -/
