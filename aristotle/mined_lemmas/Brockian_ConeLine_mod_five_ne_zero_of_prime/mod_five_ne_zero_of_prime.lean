/-
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime larger than `5` is not divisible by `5`. -/

lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h1 <;> omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` occupies all four nonzero
residue classes mod `5`, in the order `1, 3, 2, 4`; in particular `p ≡ 1 [MOD 5]`. -/
