/-
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib


set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime greater than `5` is not divisible by `5`, i.e. its residue mod `5` is nonzero. -/

lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) : q % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero hmod
  have : (5 : ℕ) = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` visits all four nonzero residues
mod `5` exactly once, in the order `(1, 3, 2, 4)`; in particular `p ≡ 1 [MOD 5]`. -/
