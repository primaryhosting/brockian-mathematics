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

lemma cycleAdj_eq_shift (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    cycleAdj n = shift n + shift n ^ (n - 1) := by
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h1 : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    rw [h1]; simp
  have h2 := two_ne_zero_zmod n hn
  ext i j
  rw [shift_pow, cycleAdj]
  simp only [Matrix.add_apply, Matrix.of_apply, shift, hcast]
  have hne : (i + 1 : ZMod n) ≠ i + (-1 : ZMod n) := by
    intro h
    exact h2 (by linear_combination h)
  by_cases h1 : j = i + 1 <;> by_cases h3 : j = i + (-1 : ZMod n) <;>
    simp_all [sub_eq_add_neg]

