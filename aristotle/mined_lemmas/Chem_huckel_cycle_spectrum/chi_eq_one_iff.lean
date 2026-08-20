/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma chi_eq_one_iff (n : ℕ) [NeZero n] (a : ZMod n) : chi n a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hd : n ∣ a.val := ((zeta_isPrimitiveRoot n).pow_eq_one_iff_dvd a.val).1 h
    have hv : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a)
    have hcast : ((a.val : ℕ) : ZMod n) = a := ZMod.natCast_rightInverse.leftInverse a
    rw [hv] at hcast
    simpa using hcast.symm
  · rintro rfl; exact chi_zero n

