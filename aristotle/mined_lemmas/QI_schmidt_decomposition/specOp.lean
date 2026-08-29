import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/

noncomputable def specOp {ι : Type} [Fintype ι] (c : ι → ℝ)
    (e : ι → EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  ∑ k, (c k : ℂ) • (LinearMap.smulRight ((innerSL ℂ (e k)) : _ →ₗ[ℂ] ℂ) (e k))

