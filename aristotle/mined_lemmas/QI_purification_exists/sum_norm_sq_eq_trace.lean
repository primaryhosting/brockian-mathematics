/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/

theorem sum_norm_sq_eq_trace [Fintype n] [Fintype m] (A : Matrix n m ℂ) :
    ((∑ p : n × m, ‖A p.1 p.2‖ ^ 2 : ℝ) : ℂ) = (A * Aᴴ).trace := by
  push_cast
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [← Complex.mul_conj' (A i k)]; simp

end Defs

/-- If two linear maps `f g : E →ₗ[ℂ] F` into a finite dimensional inner product space have the
same "length function" `‖f x‖ = ‖g x‖`, then `g` is obtained from `f` by composing with a linear
isometry of `F`.  (This is the abstract form of the uniqueness of purifications.) -/
