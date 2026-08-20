import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
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

namespace Math2

open Matrix

variable {n : ℕ}

/-- The standard symplectic form on `ℝ ^ (2 * n)`, with `ℝ ^ (2 * n)` modelled as functions
`(Fin n ⊕ Fin n) → ℝ`: the coordinates indexed by `Sum.inl i` are the positions `qᵢ` and the
coordinates indexed by `Sum.inr i` are the momenta `pᵢ`. -/

lemma omegaForm_mulVec {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ) (x y : (Fin n ⊕ Fin n) → ℝ) :
    omegaForm (A *ᵥ x) (A *ᵥ y) = omegaForm x y := by
  have hA' : Aᵀ * Matrix.J (Fin n) ℝ * A = Matrix.J (Fin n) ℝ := SymplecticGroup.mem_iff'.1 hA
  rw [omegaForm_eq_dotProduct, omegaForm_eq_dotProduct]
  congr 1
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']

/-- The key algebraic consequence of the symplectic condition `A * J * Aᵀ = J`: the two rows of `A`
indexed by `Sum.inl i₀` and `Sum.inr i₀` pair to `1` under the symplectic form. -/
