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

/-- A `k`-tuple `H : Fin k → ℕ` is *admissible* when, for every prime `p`, the values
`H i` do not cover all residue classes modulo `p`. -/

def IsAdmissibleKTuple (k : ℕ) (H : Fin k → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i : Fin k, (H i : ZMod p) ≠ r

/-- Key intermediate lemma: a `k`-tuple automatically misses a residue class modulo any
modulus `p` with `k < p`, simply because there are too few values to be surjective. -/
