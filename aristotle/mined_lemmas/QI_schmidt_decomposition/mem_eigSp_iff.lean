/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma mem_eigsp_iff (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (s : ℝ) (v : Fin m → ℂ) :
    v ∈ eigsp ψ s ↔ ∀ p, ∑ p', rho ψ p p' * v p' = (s : ℂ) ^ 2 * v p := by
  simp only [eigsp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_zero, funext_iff, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul]

/-! ### Uniqueness -/

