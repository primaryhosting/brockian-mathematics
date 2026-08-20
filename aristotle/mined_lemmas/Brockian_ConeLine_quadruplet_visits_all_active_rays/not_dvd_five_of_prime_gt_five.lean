/-
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/

lemma not_dvd_five_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : q % 5 ≠ 0 := by
  intro h0
  have : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h0
  have := (Nat.Prime.eq_one_or_self_of_dvd hq 5 this)
  omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` has residues
`1, 3, 2, 4` modulo `5`, in that order. -/
