import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

theorem ramsey_3_4 : IsLeast {n : ℕ | RamseyProp n 3 4} 9 := by
  constructor
  · exact ramsey_upper
  · intro n hn
    by_contra hlt
    exact not_ramseyProp_of_le_eight (by omega) hn

end Math


