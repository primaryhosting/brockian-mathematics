import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

theorem twinCount_le (N z k : ℕ) (hk : Even k) :
    (twinCount N : ℝ)
      ≤ (z + 1) + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)))
        + (N : ℝ) * (∏ p ∈ oddPrimesLe z, (1 + 4 / (p : ℝ))) / 2 ^ (k + 1)
        + (k + 1) * (2 * z + 3) ^ k := by
  have h1 := twinCount_le_siftCount N z
  have h2 := siftCount_le N z k hk
  have h1R : (twinCount N : ℝ) ≤ (z + 1 : ℕ) + (siftCount N z : ℝ) := by exact_mod_cast h1
  push_cast at h1R
  linarith

end Brun

