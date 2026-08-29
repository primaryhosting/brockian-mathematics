import Mathlib

/-!
# Square Ray Primes Mod 20
Category: Cone Line
Target: Brockian.ConeLine.square_ray_primes_mod20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `p` with `5 < p` is odd. -/

theorem odd_of_prime_gt_five {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) : p % 2 = 1 := by
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd
    have : (2 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd
    omega
  omega

/-- Primes on the square rays refine to four classes mod 20:
a prime `p > 5` with `p ≡ 1` or `4 (mod 5)` satisfies `p % 20 ∈ {1, 9, 11, 19}`. -/
