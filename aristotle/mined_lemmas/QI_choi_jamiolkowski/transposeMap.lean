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

def transposeMap (k : Type) : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ where
  toFun A := Aᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Choi matrix of the transpose map on `2 × 2` matrices (the swap operator) is not
positive semidefinite. -/
