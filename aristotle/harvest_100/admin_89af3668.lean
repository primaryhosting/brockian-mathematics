/-
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.ConeLine

/-- A prime `p` with `5 < p` is not divisible by `5`. -/
theorem not_five_dvd_of_prime_gt_five {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) : ¬ (5 ∣ p) := by
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdvd
  omega

/-- **Sexy prime roads.** If `p` and `p + 6` are both prime and `p > 5`, then modulo `5` the
pair `(p, p+6)` travels one of the roads `1 → 2`, `2 → 3`, `3 → 4`. In particular
`(p + 6) ≡ p + 1 (mod 5)` and neither endpoint is `0 (mod 5)`. -/
theorem sexy_prime_roads {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : ¬ (5 ∣ p) := not_five_dvd_of_prime_gt_five hp h5
  have h2 : ¬ (5 ∣ (p + 6)) := not_five_dvd_of_prime_gt_five hq (by omega)
  have h1' : p % 5 ≠ 0 := fun h => h1 (Nat.dvd_of_mod_eq_zero h)
  have h2' : (p + 6) % 5 ≠ 0 := fun h => h2 (Nat.dvd_of_mod_eq_zero h)
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

