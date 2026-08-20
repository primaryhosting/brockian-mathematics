/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/

lemma ch_ne_one {x : ZMod 13} (hx : x ≠ 0) : ch x ≠ 1 := by
  intro h
  have hval : x.val ≠ 0 := fun hv => hx ((ZMod.val_eq_zero x).mp hv)
  have hlt : x.val < 13 := ZMod.val_lt x
  have h' : Complex.exp ((x.val : ℂ) * (2 * Real.pi * Complex.I / 13)) = 1 := by
    rw [Complex.exp_nat_mul]; exact h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hz : (x.val : ℤ) = 13 * n := by exact_mod_cast hn
  omega

