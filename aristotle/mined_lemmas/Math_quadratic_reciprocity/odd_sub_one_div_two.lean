/-
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Auxiliary: for an odd natural number `n`, `(n - 1) / 2 = n / 2`. -/

theorem odd_sub_one_div_two {n : ℕ} (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **The Law of Quadratic Reciprocity**.
For distinct odd primes `p` and `q`,
`(p / q) * (q / p) = (-1) ^ (((p - 1) / 2) * ((q - 1) / 2))`,
where `(· / ·)` denotes the Legendre symbol. -/
