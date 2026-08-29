/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/

theorem rank_cutMatrix_mps_le (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (k m : ℕ) : (cutMatrix (mpsState A vL vR (k + m))).rank ≤ D := by
  rw [cutMatrix_mps_eq_mul]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using Matrix.rank_le_card_width
    (Matrix.of fun (u : Fin k → Fin d) (a : Fin D) => (vL ᵥ* mpsProd A 0 k u) a)

/-- The trace of the reduced density matrix is the squared norm of the state. -/
