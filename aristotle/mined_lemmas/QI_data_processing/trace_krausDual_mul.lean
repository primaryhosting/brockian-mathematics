import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/

theorem trace_krausDual_mul (K : ι → Matrix m n ℂ) (B : Matrix m m ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (krausDual K B * A) = Matrix.trace (B * krausMap K A) := by
  simp only [krausDual, krausMap, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_mul_comm ((K i)ᴴ * B * K i) A, Matrix.trace_mul_comm B (K i * A * (K i)ᴴ)]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (A * (K i)ᴴ * B) (K i), ← Matrix.mul_assoc, ← Matrix.mul_assoc]

end QI

import Mathlib

/-!
# The scalar integral behind the integral representation of the relative entropy

For `r ≥ 0` and `s > 0`,
`∫_0^∞ (r² / (s + t r) - r / (1 + t)) dt = r log r - r log s`.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace QI

/-- The antiderivative of `t ↦ r² / (s + t r) - r / (1 + t)`. -/
