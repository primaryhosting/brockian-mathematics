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

lemma rank_posProj {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    (posProj hQ).rank = posIndex Q := by
  rw [posProj, Matrix.rank_diagonal, posIndex_of_isHermitian hQ, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (by intro i; simp))

/-- **Easy direction of Sylvester's law**: there is a matrix whose column space is a subspace of
dimension `posIndex Q` on which the form of `Q` is positive definite. -/
