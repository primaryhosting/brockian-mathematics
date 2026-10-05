/-
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open Matrix

namespace Zeta23Redux
namespace LinAlg

/-- The quadratic form (Hermitian form) attached to a complex matrix `M`:
`qf M x = ⟪x, M x⟫ = ∑ i, ∑ j, conj (x i) * M i j * x j`. -/
noncomputable def qf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  star (x : Fin n → ℂ) ⬝ᵥ (M *ᵥ (x : Fin n → ℂ))

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

end LinAlg
end Zeta23Redux

