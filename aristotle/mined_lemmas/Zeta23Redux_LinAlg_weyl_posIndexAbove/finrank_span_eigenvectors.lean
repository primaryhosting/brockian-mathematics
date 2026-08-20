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

lemma finrank_span_eigenvectors {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (p : Fin d → Prop) [DecidablePred p] :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun i : {i // p i} => (hM.eigenvectorBasis i.1 :
          EuclideanSpace ℂ (Fin d))))
      = (Finset.univ.filter p).card := by
  have hli : LinearIndependent ℂ (fun i : {i // p i} => (hM.eigenvectorBasis i.1 :
      EuclideanSpace ℂ (Fin d))) :=
    (hM.eigenvectorBasis.orthonormal.linearIndependent).comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

end Span

/-- **Weyl monotonicity**: if all eigenvalues of the Hermitian perturbation `E` are bounded
in absolute value by `θ`, then the number of eigenvalues of `A + E` strictly above `θ`
is at most the number of strictly positive eigenvalues of `A`. -/
