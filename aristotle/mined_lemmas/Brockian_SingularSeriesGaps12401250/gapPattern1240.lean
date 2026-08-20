import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of nonnegative integer offsets (a "gap pattern") is *admissible* if for
every prime `p` the offsets fail to cover all residue classes modulo `p`.  Equivalently,
the singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` attached to `H` in the
Hardy–Littlewood prime `k`-tuple conjecture is nonzero. -/

def gapPattern1240 : Finset ℕ := {0, 4, 6, 10, 12, 16}

/-- The octuple pattern `{0, 2, 6, 8, 12, 18, 20, 26}` of diameter `26`. -/
