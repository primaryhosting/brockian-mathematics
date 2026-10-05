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

import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `n > 5` is not divisible by `5`. -/
theorem not_five_dvd_of_prime_gt_five {n : ℕ} (hn : n.Prime) (h : 5 < n) : n % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero hmod
  rcases hn.eq_one_or_self_of_dvd 5 hdvd with h1 | h2 <;> omega

/-- Sexy primes `(p, p + 6)` with `p > 5` travel exactly the roads `1 → 2`, `2 → 3`, `3 → 4`
modulo `5`: neither endpoint sits on ray `0`, and `(p + 6) ≡ p + 1 [MOD 5]`. -/
theorem sexy_prime_roads (p : ℕ) (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hp5 : p % 5 ≠ 0 := not_five_dvd_of_prime_gt_five hp h5
  have hq5 : (p + 6) % 5 ≠ 0 := not_five_dvd_of_prime_gt_five hq (by omega)
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

