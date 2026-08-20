import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem om_pow_ne_one {t : ℕ} (ht : t % 9 ≠ 0) : om ^ t ≠ 1 := by
  intro h
  have hdvd : (9 : ℕ) ∣ t := (om_primitive.pow_eq_one_iff_dvd _).1 h
  omega

