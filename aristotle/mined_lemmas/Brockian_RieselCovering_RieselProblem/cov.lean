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

def cov : Nat → Nat
  | 0 => 3
  | 1 => 5
  | 2 => 3
  | 3 => 241
  | 4 => 3
  | 5 => 5
  | 6 => 3
  | 7 => 13
  | 8 => 3
  | 9 => 5
  | 10 => 3
  | 11 => 7
  | 12 => 3
  | 13 => 5
  | 14 => 3
  | 15 => 17
  | 16 => 3
  | 17 => 5
  | 18 => 3
  | 19 => 13
  | 20 => 3
  | 21 => 5
  | 22 => 3
  | _ => 7

/-- The cofactor witnessing `509203 * 2 ^ r ≡ 1 (mod cov r)`. -/
