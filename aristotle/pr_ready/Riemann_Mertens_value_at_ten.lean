/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Statement: The Mertens function M(10) = sum_{k=1}^{10} mu(k) = -1, where mu is the Moebius function. (RH is equivalent to M(n) = O(n^{1/2+eps}).) Compute via Mathlib's ArithmeticFunction.moebius.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is Mathlib's Möbius function
`ArithmeticFunction.moebius`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

/-- `M 10 = ∑_{k=1}^{10} μ k = -1`. -/
theorem value_at_ten : mertens 10 = -1 := by
  unfold mertens
  decide +kernel

/-- The same statement written out as an explicit sum of Möbius values. -/
theorem sum_moebius_Icc_one_ten : ∑ k ∈ Finset.Icc 1 10, moebius k = -1 :=
  value_at_ten

end Riemann.Mertens


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

