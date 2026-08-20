import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras, acting on
`k × n` block matrices: the `(x, y)` block of `M` (an `n × n` matrix) is sent to the
`(x, y)` block of the result (an `m × m` matrix). -/

noncomputable def choiEquiv :
    (Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) ≃ₗ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun := choi
  map_add' Φ Ψ := by ext p q; simp [choi]
  map_smul' c Φ := by ext p q; simp [choi]
  invFun := ofChoi
  left_inv Φ := by
    ext X a b
    simpa [ofChoi] using (apply_eq_sum_choi Φ X a b).symm
  right_inv C := by
    ext p q
    simp [choi, ofChoi, Matrix.single, ite_and]

omit [Fintype m] [DecidableEq m] in
