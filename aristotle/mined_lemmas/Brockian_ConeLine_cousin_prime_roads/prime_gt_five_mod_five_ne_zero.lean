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
