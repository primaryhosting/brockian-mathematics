import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including this
module docstring, so the header comment appears immediately after the single import.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₈`, over `ℂ`. -/

lemma adj_mul_U : C8adj * U = U * Matrix.diagonal lam := by
  ext i k
  have hne : (i - 1 : Fin 8) ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hleft : ∑ j, C8adj i j * U j k = U (i - 1) k + U (i + 1) k := by
    rw [show (∑ j, C8adj i j * U j k) = (((cycleGraph 8).adjMatrix ℂ) *ᵥ fun j => U j k) i from rfl]
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
      Finset.sum_pair hne]
  rw [hleft]
  have hright : ∑ x, U i x * (Matrix.diagonal lam) x k = U i k * lam k := by
    simp [Matrix.diagonal_apply]
  rw [hright]
  have h1 : U (i - 1) k = chi ((i - 1) * k) := by rw [chi_mul_val, U_apply]
  have h2 : U (i + 1) k = chi ((i + 1) * k) := by rw [chi_mul_val, U_apply]
  have h3 : U i k = chi (i * k) := by rw [chi_mul_val, U_apply]
  rw [h1, h2, h3, lam]
  have e1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have e2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [e1, e2, chi_add, chi_add]
  ring

/-- The characteristic polynomial of the adjacency matrix of `C₈` splits as the product over
`k = 0, …, 7` of `X - 2cos(2πk/8)`, and the spectrum is exactly the set of these numbers:
the Hückel eigenvalues of cyclooctatetraene. -/
