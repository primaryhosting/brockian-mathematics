/-
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/

theorem not_dvd_five_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : ¬ (5 ∣ q) := by
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/--
A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible residue patterns
modulo `5`: `(1, 3, 2)` or `(2, 4, 3)`.
-/
