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
