/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to come before any module docstring, so the header
-- above is reproduced verbatim as the module docstring immediately after the imports.)

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ComplexOrder InnerProductSpace

/-! ## States on a unital ⋆-algebra over `ℂ` -/

/-- A *state* on a unital `ℂ`-⋆-algebra `A`: a positive, normalized linear functional. -/
structure IsState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) : Prop where
  /-- Positivity: `phi (a⋆ * a)` is a nonnegative real number. -/
  nonneg : ∀ a : A, 0 ≤ phi (star a * a)
  /-- Normalization. -/
  map_one : phi 1 = 1

namespace IsState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {phi : A →ₗ[ℂ] ℂ}


lemma isState_vectorState {e : H} (he : ‖e‖ = 1) : IsState (vectorState e) where
  nonneg a := by
    have hstar : (star a * a) e = ContinuousLinearMap.adjoint a (a e) := rfl
    rw [vectorState_apply, hstar, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    simp [Complex.le_def]
  map_one := by
    rw [vectorState_apply]
    simp [inner_self_eq_norm_sq_to_K, he]

/-- The statement of the **Kadison–Singer problem** for the atomic MASA determined by an
orthonormal basis `b` of a Hilbert space `H`: any two states of `B(H)` that agree on the
diagonal operators, and whose common restriction to the diagonal operators is multiplicative
(equivalently: is a *pure* state of that abelian subalgebra), are equal.

This is the property established by Marcus, Spielman and Srivastava (2015) using interlacing
families of characteristic polynomials. It is recorded here for reference; the atomic case is
proved below in `Frontier.kadison_singer`. -/
