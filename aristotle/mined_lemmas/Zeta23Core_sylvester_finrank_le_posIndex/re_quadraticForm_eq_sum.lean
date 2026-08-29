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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of positive eigenvalues. -/

lemma re_quadraticForm_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) =
      ∑ i, hA.eigenvalues i * ‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i‖ ^ 2 := by
  rw [quadraticForm_eq_sum hA x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x)) i *
      ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i =
      ((‖((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [this, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The `𝕜`-linear map sending a vector to the coordinates, in the eigenvector basis, that
correspond to positive eigenvalues. -/
