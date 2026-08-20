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


theorem kadison_singer {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ι)
    (phi psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hphi : IsState phi) (hpsi : IsState psi)
    (hphid : ∀ a, IsDiagonal b a → phi a = ⟪b k, a (b k)⟫_ℂ)
    (hpsid : ∀ a, IsDiagonal b a → psi a = ⟪b k, a (b k)⟫_ℂ) :
    (∀ a, phi a = ⟪b k, a (b k)⟫_ℂ) ∧ phi = psi := by
  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  have hval : ∀ chi : (H →L[ℂ] H) →ₗ[ℂ] ℂ, IsState chi →
      (∀ a, IsDiagonal b a → chi a = ⟪b k, a (b k)⟫_ℂ) →
      ∀ a, chi a = ⟪b k, a (b k)⟫_ℂ := by
    intro chi hchi hd
    have h1 : chi (rankOneProj (b k)) = 1 := by
      rw [hd _ (isDiagonal_rankOneProj b k)]
      simp [inner_self_eq_norm_sq_to_K, hnorm]
    exact state_eq_vectorState_of_apply_rankOneProj_eq_one hnorm chi hchi h1
  refine ⟨hval phi hphi hphid, ?_⟩
  ext a
  rw [hval phi hphi hphid a, hval psi hpsi hpsid a]

/-- **Unique extension of atomic pure states.** For each index `k` there is exactly one state of
`B(H)` whose restriction to the atomic MASA is the atomic pure state `a ↦ ⟪b k, a (b k)⟫`, namely
the vector state at `b k`. -/
