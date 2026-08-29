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

noncomputable def posCoords {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (n → 𝕜) →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
  (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i : n // 0 < hA.eigenvalues i} → n)).comp
    (Matrix.mulVecLin (star (hA.eigenvectorUnitary : Matrix n n 𝕜)))

@[simp]
