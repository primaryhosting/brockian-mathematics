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

theorem cutMatrix_mps_eq_mul (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (k m : ℕ) :
    cutMatrix (mpsState A vL vR (k + m)) =
      (Matrix.of fun (u : Fin k → Fin d) (a : Fin D) => (vL ᵥ* mpsProd A 0 k u) a) *
      (Matrix.of fun (a : Fin D) (v : Fin m → Fin d) => (mpsProd A k m v *ᵥ vR) a) := by
  ext u v
  rw [Matrix.mul_apply]
  show mpsState A vL vR (k + m) (Fin.append u v) = _
  unfold mpsState
  rw [mpsProd_append A 0 k m u v, zero_add, dotProduct_mul_mulVec]
  rfl

/-- **Bond-dimension bound on the Schmidt rank.** The rank of the cut matrix of an MPS is at
most the bond dimension `D`, independently of the number of sites on either side of the cut. -/
