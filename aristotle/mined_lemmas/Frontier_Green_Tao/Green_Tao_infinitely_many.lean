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

theorem Green_Tao_infinitely_many (h : ErdosTuranStatement) (k : ℕ) :
    {a : ℕ | ∃ d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)}.Infinite :=
  (Green_Tao h).infinite_starting_points k

/-! ### Structure of arithmetic progressions of primes

The following unconditional results describe the shape that any long progression of primes
must have: its common difference is divisible by every prime `p ≤ k` (hence by the primorial
`k#`), unless the progression itself starts at such a small prime. -/

/-- If `a, a + d, …, a + (k-1) d` are all prime and `p ≤ k` is a prime smaller than the first
term `a`, then `p` divides the common difference `d`. -/
