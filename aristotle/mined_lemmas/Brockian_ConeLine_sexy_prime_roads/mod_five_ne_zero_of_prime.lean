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
