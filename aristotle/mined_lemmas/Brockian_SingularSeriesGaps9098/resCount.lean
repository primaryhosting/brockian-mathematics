/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The number of residue classes modulo `p` occupied by a finite set `H` of natural numbers.
This is the quantity `ν_H(p)` appearing in the Euler factors of the Hardy–Littlewood
singular series of the tuple `H`. -/

def resCount (H : Finset ℕ) (p : ℕ) : ℕ := (H.image (· % p)).card

/-- A finite set `H ⊆ ℕ` (a "gap pattern") is *admissible* when, for every prime `p`, some
residue class modulo `p` is missed by `H`. Equivalently, every Euler factor of the singular
series of `H` is nonzero. -/
