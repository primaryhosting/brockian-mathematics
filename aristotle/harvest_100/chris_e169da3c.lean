/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Brockian
namespace ConeLine

/-- If `n` is prime and `5 < n`, then `n % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime {n : ℕ} (hn : Nat.Prime n) (h : 5 < n) : n % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 hdvd) with h1 | h2
  · omega
  · omega

/-- Sexy primes `(p, p + 6)` with `p > 5` travel exactly the roads `1 → 2`, `2 → 3`, `3 → 4`
modulo `5`. -/
theorem sexy_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have h3 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h4 : (p + 6) % 5 = (p % 5 + 1) % 5 := by omega
  simp only [Prod.mk.injEq]
  omega

end ConeLine
end Brockian

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

