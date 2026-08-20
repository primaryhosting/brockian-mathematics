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

theorem choi_transposeMap_not_posSemidef :
    ¬ (choiMatrix (transposeMap (Fin 2))).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg
    (fun x => if x = (0, 1) then 1 else if x = (1, 0) then -1 else 0)
  simp only [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.single_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.star_apply] at hv
  norm_num at hv

/-- Consequently the transpose map is not completely positive. -/
