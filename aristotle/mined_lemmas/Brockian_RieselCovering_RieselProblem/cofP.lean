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

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- `IsComposite N` means that `N` factors as a product of two factors, each `> 1`. -/

def cofP (r : Nat) : Nat := (2 ^ 24 - 1) / cov r

/-- The covering data, checked residue by residue: for each `r < 24` the number `cov r`
lies strictly between `1` and `242`, divides `2 ^ 24 - 1`, and satisfies
`509203 * 2 ^ r ≡ 1 (mod cov r)`. -/
