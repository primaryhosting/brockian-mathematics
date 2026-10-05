import Mathlib
/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian
namespace ConeLine

/-- A prime `p` with `5 < p` is not divisible by `5`. -/
theorem prime_gt_five_mod_five_ne_zero {p : ℕ} (hp : p.Prime) (h5 : 5 < p) :
    p % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
  rcases hp.eq_one_or_self_of_dvd 5 hdvd with h1 | h2
  · omega
  · omega

/-- Cousin primes `(p, p+4)` with `p > 5` travel exactly the roads
`2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel: `p % 5 ∈ {2,3,4}` and
`(p + 4) % 5 = p % 5 - 1`. -/
theorem cousin_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime) (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : p % 5 ≠ 0 := prime_gt_five_mod_five_ne_zero hp h5
  have h2 : (p + 4) % 5 ≠ 0 := prime_gt_five_mod_five_ne_zero hq (by omega)
  have hcases : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases hcases with h | h | h <;> simp only [Prod.mk.injEq] <;> omega

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

