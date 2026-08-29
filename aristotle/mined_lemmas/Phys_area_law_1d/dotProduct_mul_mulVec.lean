/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/

private theorem dotProduct_mul_mulVec (P Q : Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ) :
    vL ⬝ᵥ ((P * Q) *ᵥ vR) = ∑ a, (vL ᵥ* P) a * (Q *ᵥ vR) a := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [sum_comm_first_last (fun b c a => vL b * (P b a * Q a c * vR c))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The cut matrix of an MPS factors through the `D`-dimensional bond space at the cut. -/
