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

noncomputable def ofChoi (C : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun X := Matrix.of fun a b => ∑ i, ∑ j, X i j * C (i, a) (j, b)
  map_add' X Y := by
    ext a b
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    simp [Finset.mul_sum, mul_assoc]

/-- **The Choi–Jamiołkowski isomorphism** as a linear equivalence: linear maps
`Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ` correspond bijectively (and linearly) to matrices on
`n × m`, via the Choi matrix. -/
