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

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/

lemma qform_eq_re_dotProduct (Q : Matrix m m 𝕜) (x : EuclideanSpace 𝕜 m) :
    qform Q x = RCLike.re (star x.ofLp ⬝ᵥ Q *ᵥ x.ofLp) := by
  rw [qform, EuclideanSpace.inner_eq_star_dotProduct, toEuclideanLin_apply']
  simp [dotProduct_comm]

/-- The quadratic form of the compression `Bᴴ Q B` is the quadratic form of `Q` evaluated at the
image vector `B x`. -/
