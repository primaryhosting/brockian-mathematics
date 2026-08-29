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

lemma sum_evals (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    ∑ j, evals ψ j = 1 := by
  have htr : (rho ψ).trace = ∑ j, (evals ψ j : ℂ) :=
    (rho_isHermitian ψ).trace_eq_sum_eigenvalues
  have hinner : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have htr2 : (rho ψ).trace = (inner ℂ ψ ψ : ℂ) := by
    rw [Matrix.trace]
    rw [inner_coord, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, rho_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [mul_comm]
  rw [htr2, hinner] at htr
  exact_mod_cast htr.symm

