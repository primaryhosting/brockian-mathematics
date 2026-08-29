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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of indices `i` such that
the `i`-th eigenvalue is positive (i.e. the number of positive eigenvalues, counted with
multiplicity). -/

lemma posCoords_apply {A : Matrix n n 𝕜} (hA : A.IsHermitian) (x : n → 𝕜)
    (i : {i : n // 0 < hA.eigenvalues i}) :
    posCoords hA x i = (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i.1 := rfl

/-- **Sylvester's law of inertia**, hard direction: if the Hermitian form associated with a
Hermitian matrix `A` is positive definite on a submodule `W` of `n → 𝕜`, then the dimension of
`W` is at most the number of positive eigenvalues of `A`. -/
