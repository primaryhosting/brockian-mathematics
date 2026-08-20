import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

/-!
## Inertia does not increase under compression

For a Hermitian matrix `Q` on a finite type `m` and a rectangular matrix `B : Matrix m d 𝕜`, the
compression `Bᴴ * Q * B` is Hermitian and its positive index of inertia (the number of positive
eigenvalues, counted with multiplicity) is at most that of `Q`.

The proof follows the variational route.  Writing `qform Q x = Re (xᴴ Q x)`, we prove both
directions of the (finite dimensional) Sylvester characterisation of the positive index:

* `Zeta23Core.exists_posdef_matrix`: the column space of `U * posProj` — where `U` diagonalises `Q`
  and `posProj` projects onto the positive eigen-directions — is a subspace of dimension
  `posIndex Q` on which `qform Q` is positive definite;
* `Zeta23Core.finrank_le_posIndex`: any subspace on which `qform Q` is positive definite has
  dimension at most `posIndex Q` (it meets the "non-positive" subspace `ker (posProj * Uᴴ)`
  trivially, and that kernel has codimension `posIndex Q`).

For the compression, such a subspace for `Bᴴ Q B` is pushed forward by `B`; injectivity on it is
forced by positive definiteness, so the dimension is preserved.
-/

namespace Zeta23Core

open Matrix Module

section Defs

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real) quadratic form `x ↦ Re (xᴴ Q x)` attached to a matrix `Q`. -/

lemma qform_eq_sum {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (x : n → 𝕜) :
    qform Q x =
      ∑ i, hQ.eigenvalues i * ‖(star (hQ.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  have hU : ((star (hQ.eigenvectorUnitary : Matrix n n 𝕜))ᴴ)
      = (hQ.eigenvectorUnitary : Matrix n n 𝕜) := by
    simp [Matrix.star_eq_conjTranspose]
  have hspec : Q = (star (hQ.eigenvectorUnitary : Matrix n n 𝕜))ᴴ *
      diagonal (fun i => (RCLike.ofReal (hQ.eigenvalues i) : 𝕜)) *
      (star (hQ.eigenvectorUnitary : Matrix n n 𝕜)) := by
    rw [hU]
    exact hQ.spectral_theorem
  conv_lhs => rw [hspec]
  rw [qform_conj, qform_diagonal]

/-- The diagonal matrix projecting onto the positive eigen-directions of `Q`. -/
