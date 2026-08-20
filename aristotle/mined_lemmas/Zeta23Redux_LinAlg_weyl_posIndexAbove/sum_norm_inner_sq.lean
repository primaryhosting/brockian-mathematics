import Mathlib

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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above

Category: Zeta-23 §3 Linear Algebra (re-derivation)

Target: `Zeta23Redux.LinAlg.weyl_posIndexAbove`

For a Hermitian matrix `A` over `ℂ` of size `Fin d` we define

* `posIndex hA`, the number of strictly positive eigenvalues of `A`;
* `posIndexAbove hA θ`, the number of eigenvalues of `A` strictly above `θ`.

The main result `weyl_posIndexAbove` is Weyl's monotonicity statement: if all eigenvalues of a
Hermitian perturbation `E` are bounded in absolute value by `θ`, then
`posIndexAbove (A + E) θ ≤ posIndex A`.

The proof is the Courant–Fischer/interlacing argument in its subspace form: the span of the
eigenvectors of `A + E` with eigenvalue `> θ` intersects trivially the span of the eigenvectors of
`A` with eigenvalue `≤ 0`, because on the first subspace the quadratic form of `A + E` is `> θ‖x‖²`
while on the second one it is `≤ 0 + θ‖x‖²`.  Comparing dimensions gives the claim.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma sum_norm_inner_sq (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) :
    ∑ i, ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have key := hM.eigenvectorBasis.sum_inner_mul_inner x x
  have h2 : ∀ i : Fin d, (inner ℂ x (hM.eigenvectorBasis i) : ℂ) * inner ℂ (hM.eigenvectorBasis i) x
      = ((‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm x (hM.eigenvectorBasis i), RCLike.conj_mul]
    push_cast; rfl
  simp_rw [h2, ← Complex.ofReal_sum] at key
  rw [inner_self_eq_norm_sq_to_K] at key
  have h3 : ((∑ i, ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [key]; push_cast; rfl
  exact Complex.ofReal_inj.mp h3

/-- The quadratic form of a Hermitian matrix expressed through its eigenvalues. -/
