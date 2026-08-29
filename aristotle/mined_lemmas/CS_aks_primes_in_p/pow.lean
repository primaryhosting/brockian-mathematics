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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem pow {f g : R[X]} (h : Cong r f g) (e : ℕ) : Cong r (f ^ e) (g ^ e) := by
  induction e with
  | zero => simpa using Cong.refl r 1
  | succ k ih => simpa [_root_.pow_succ] using ih.mul h

end Cong

/-- `X ^ a ≡ X ^ (a % r)` modulo `X ^ r - 1`. -/
