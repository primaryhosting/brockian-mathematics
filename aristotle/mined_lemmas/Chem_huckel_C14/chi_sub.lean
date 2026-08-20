import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_sub (a b : Fin 14) : chi (a - b) = chi a * (chi b)⁻¹ := by
  have hab : a - b + b = a := sub_add_cancel a b
  have h : chi (a - b) * chi b = chi a := by rw [← chi_add, hab]
  rw [← h, mul_assoc, mul_inv_cancel₀ (chi_ne_zero b), mul_one]

