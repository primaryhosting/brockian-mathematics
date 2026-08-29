import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma chi_eq_one_iff (a : ZMod 15) : chi a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have h15 : (15 : ℕ) ∣ a.val := (zeta_isPrimitiveRoot.pow_eq_one_iff_dvd a.val).mp h
    have hlt := ZMod.val_lt a
    have hv : a.val = 0 := by
      rcases Nat.eq_zero_or_pos a.val with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 h15) (by omega)
    exact (ZMod.val_eq_zero a).mp hv
  · rintro rfl; exact chi_zero

