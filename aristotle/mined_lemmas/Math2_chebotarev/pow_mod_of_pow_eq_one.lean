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

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {q : ℕ} {x : M}
    (hx : x ^ q = 1) (m : ℕ) : x ^ m = x ^ (m % q) := by
  conv_lhs => rw [← Nat.div_add_mod m q]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- `σ` is a Frobenius element at `p` for the `q`-th cyclotomic extension of `ℚ` if it acts
on the `q`-th roots of unity as the `p`-th power map. -/
