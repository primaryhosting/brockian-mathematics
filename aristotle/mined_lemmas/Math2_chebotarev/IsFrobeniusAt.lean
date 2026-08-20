/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

namespace Math2

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

def IsFrobeniusAt (q p : ℕ) (σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) : Prop :=
  ∀ x : CyclotomicField q ℚ, x ^ q = 1 → σ x = x ^ p

/-- Each element of the Galois group is the Frobenius exactly at the natural numbers in a
fixed invertible residue class mod `q`. -/
