import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia `n₊(A)` of a Hermitian matrix `A`: the number of indices `i`
for which the `i`-th eigenvalue of `A` is positive. -/

theorem re_dotProduct_mulVec_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hAx : A *ᵥ x = U *ᵥ ((diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ y) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, hy, hU]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hAx, dotProduct_mulVec, hstar, dotProduct]
  simp only [mulVec_diagonal, Pi.star_apply, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (star (y i) * ((hA.eigenvalues i : 𝕜) * y i))
      = (hA.eigenvalues i : 𝕜) * (star (y i) * y i) by ring, RCLike.star_def, RCLike.conj_mul]
  simp

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a subspace `W` of `n → 𝕜`, then
`dim W ≤ n₊(A)`, the number of positive eigenvalues of `A`. -/
