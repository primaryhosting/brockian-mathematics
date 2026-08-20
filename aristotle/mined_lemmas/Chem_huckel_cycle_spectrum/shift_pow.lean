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

lemma shift_pow (n : ℕ) [NeZero n] (m : ℕ) :
    shift n ^ m = Matrix.of fun i j => if j = i + (m : ZMod n) then 1 else 0 := by
  induction m with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ m ih =>
      ext i j
      rw [pow_succ, Matrix.mul_apply, ih]
      rw [Finset.sum_eq_single (i + (m : ZMod n))]
      · simp [shift, add_assoc]
      · intro b _ hb
        simp [hb, shift]
      · simp

