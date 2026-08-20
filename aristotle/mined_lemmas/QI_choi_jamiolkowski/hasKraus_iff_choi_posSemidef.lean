/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

theorem hasKraus_iff_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    HasKraus Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨fun h => choi_posSemidef_of_isCompletelyPositive Φ (isCompletelyPositive_of_hasKraus Φ h),
    hasKraus_of_choi_posSemidef Φ⟩

/-! ### The transpose map is not completely positive

This shows the notions above are not vacuous. -/

/-- The transpose map on matrices, as a linear map. -/
