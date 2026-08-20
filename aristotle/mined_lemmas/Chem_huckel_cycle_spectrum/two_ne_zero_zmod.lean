/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

lemma two_ne_zero_zmod (n : ℕ) [NeZero n] (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro hc
  have h : ((2 : ℕ) : ZMod n) = 0 ↔ (n ∣ 2) := ZMod.natCast_eq_zero_iff 2 n
  have hd : n ∣ 2 := h.mp (by exact_mod_cast hc)
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-- The cycle adjacency matrix is the sum of the cyclic shift and its inverse. -/
