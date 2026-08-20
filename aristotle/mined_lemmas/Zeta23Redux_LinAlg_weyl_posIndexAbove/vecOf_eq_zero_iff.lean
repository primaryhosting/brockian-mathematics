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

open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma vecOf_eq_zero_iff (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (S : Finset (Fin d)) (c : S → ℂ) : vecOf b S c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext i
    have := repr_vecOf b S c i
    rw [h] at this
    simpa [i.2] using this.symm
  · rintro rfl
    simp only [vecOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, dite_eq_ite, ite_self]
    rw [show (WithLp.toLp 2 (fun _ : Fin d => (0 : ℂ))) = 0 from rfl, map_zero]

/-- **Weyl monotonicity** for the counting functions: if all eigenvalues of the Hermitian
perturbation `E` are bounded in absolute value by `θ`, then the number of eigenvalues of
`A + E` above `θ` is at most the number of positive eigenvalues of `A`. -/
