/-
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

open Matrix Unitary

namespace Zeta23Core

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/

lemma re_quadratic_form_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set y : n → 𝕜 := star U *ᵥ x with hy
  have hstar : star y = vecMul (star x) U := by
    rw [hy, star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
  have h1 : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    conv_lhs => rw [spectral_mul_form hA]
    rw [← hU, ← mulVec_mulVec, ← mulVec_mulVec, ← hy, dotProduct_mulVec, hstar]
  rw [h1, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (y i) * ((diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) i)
      = ((hA.eigenvalues i : 𝕜)) * (star (y i) * y i) := by
    rw [mulVec_diagonal]
    simp [Function.comp]
    ring
  rw [Pi.star_apply, this, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **Sylvester's law of inertia**, hard direction: if a Hermitian matrix `A` is positive
definite on a subspace `W`, then `dim W ≤ n₊(A)`, the number of positive eigenvalues of `A`. -/
