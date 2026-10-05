import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime `p` with `5 < p` is not divisible by `5`. -/
lemma not_five_dvd_of_prime_gt_five {p : ℕ} (hp : p.Prime) (h5 : 5 < p) : ¬ (5 ∣ p) := by
  intro h
  have : (5 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h
  omega

/-- Sexy primes (`p` and `p + 6` both prime, `p > 5`) travel exactly the roads
`1 → 2`, `2 → 3`, `3 → 4` modulo `5`: neither endpoint can sit on ray `0`. -/
theorem sexy_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : ¬ (5 ∣ p) := not_five_dvd_of_prime_gt_five hp h5
  have h2 : ¬ (5 ∣ (p + 6)) := not_five_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h1 h2
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

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

