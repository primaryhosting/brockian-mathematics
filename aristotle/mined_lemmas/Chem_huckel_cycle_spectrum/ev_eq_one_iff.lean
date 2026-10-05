/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma ev_eq_one_iff (a : Fin n) : ev a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hdvd : n ∣ (a : ℕ) :=
      ((isPrimitiveRoot_zeta (n := n)).pow_eq_one_iff_dvd (a : ℕ)).1 h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd a.isLt)
  · rintro rfl; exact ev_zero

/-- Orthogonality of the characters: `∑ k, ev (k * m)` is `n` if `m = 0` and `0` otherwise. -/
