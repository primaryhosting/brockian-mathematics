import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
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

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`: there are a starting point `a`
and a positive common difference `d` with `a, a + d, …, a + (k-1) d` all in `A`. -/

theorem primorial_dvd_common_difference {a d k : ℕ} (hka : k < a)
    (hprime : ∀ i < k, Nat.Prime (a + i * d)) : primorial k ∣ d := by
  refine Finset.prod_primes_dvd d ?_ ?_ <;> intro q hq <;>
    simp only [Finset.mem_filter, Finset.mem_range] at hq
  · exact hq.2.prime
  · exact prime_dvd_common_difference hprime hq.2 (by omega) (by omega)

/-- Consequently, the common difference of a `k`-term progression of primes starting above `k`
is at least the primorial `k#`; long progressions of primes necessarily have huge gaps. -/
