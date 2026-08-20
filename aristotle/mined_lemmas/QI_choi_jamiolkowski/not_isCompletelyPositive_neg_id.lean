/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : ℕ}

/-- A linear map between spaces of square complex matrices. -/
abbrev MatMap (n m : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ

/-- The Choi matrix of a linear map `Φ`:
`C_{(a,s),(b,t)} = Φ(E_{ab})_{s,t}`, i.e. `C = ∑_{a,b} E_{ab} ⊗ Φ(E_{ab})`. -/

lemma not_isCompletelyPositive_neg_id :
    ¬ IsCompletelyPositive (-LinearMap.id : MatMap 1 1) := by
  rw [choi_jamiolkowski]
  intro h
  have h2 : (0 : ℂ) ≤ choiMatrix (-LinearMap.id : MatMap 1 1) (0, 0) (0, 0) := h.diag_nonneg
  simp only [choiMatrix, Matrix.of_apply, LinearMap.neg_apply, LinearMap.id_apply,
    Matrix.neg_apply, Matrix.single_apply] at h2
  norm_num at h2

end QI

