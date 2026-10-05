/-
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/

lemma not_five_dvd_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) : q % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero hmod
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible
residue ("ray") patterns mod 5: `(1,3,2)` or `(2,4,3)`. -/
