/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma z19_ne_one {x : ZMod 19} (hx : x ≠ 0) : z19 x ≠ 1 := by
  intro h
  rw [z19, g, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  field_simp at hn
  have hz : ((x.val : ℤ) : ℂ) = ((19 * n : ℤ) : ℂ) := by push_cast; linear_combination hn
  have hzz : (x.val : ℤ) = 19 * n := by exact_mod_cast hz
  have hdvd : (19 : ℤ) ∣ (x.val : ℤ) := ⟨n, hzz⟩
  have h19 : (19 : ℕ) ∣ x.val := by exact_mod_cast hdvd
  have hlt : x.val < 19 := ZMod.val_lt x
  have hne : x.val ≠ 0 := by
    simpa [ZMod.val_eq_zero] using hx
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h19
  omega

