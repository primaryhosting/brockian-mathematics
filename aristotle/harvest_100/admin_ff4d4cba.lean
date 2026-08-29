import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- If `q` is a prime greater than `5`, then `5` does not divide `q`. -/
lemma five_not_dvd_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : ¬ (5 ∣ q) := by
  intro hdvd
  have : (5 : ℕ) = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- Sexy primes travel exactly the roads `1→2`, `2→3`, `3→4` modulo `5`. -/
theorem sexy_prime_roads (p : ℕ) (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : ¬ (5 ∣ p) := five_not_dvd_of_prime_gt_five hp h5
  have h2 : ¬ (5 ∣ (p + 6)) := five_not_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h1 h2
  have e1 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have e2 : (p + 6) % 5 = (p % 5 + 1) % 5 := by omega
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

