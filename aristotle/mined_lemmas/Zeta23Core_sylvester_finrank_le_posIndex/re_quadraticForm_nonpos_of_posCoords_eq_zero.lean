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

lemma re_quadraticForm_nonpos_of_posCoords_eq_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {x : n → 𝕜} (hx : posCoords hA x = 0) :
    RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ 0 := by
  rw [re_quadraticForm_eq_sum hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases le_or_gt (hA.eigenvalues i) 0 with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  · have : ((star (hA.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i = 0 := by
      have := congrFun hx ⟨i, h⟩
      simpa [posCoords] using this
    simp [this]

/-- **Sylvester's law of inertia**, hard direction: if a Hermitian matrix `A` defines a positive
definite form on a subspace `W`, then `dim W ≤ n₊(A)`, the number of positive eigenvalues
of `A`. -/
