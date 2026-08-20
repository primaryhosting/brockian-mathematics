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

lemma geom_vec_succ (n : ℕ) [NeZero n] (μ : ℂ) (h : μ ^ n = 1) (i : ZMod n) :
    μ ^ (i + 1 : ZMod n).val = μ * μ ^ i.val := by
  have hi : (i + 1 : ZMod n) = ((i.val + 1 : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  have hval : (i + 1 : ZMod n).val = (i.val + 1) % n := by
    rw [hi, ZMod.val_natCast]
  rw [hval, pow_val_mod μ n h, pow_succ]
  ring

