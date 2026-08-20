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


def KadisonSingerUniqueExtension {ι : Type*} (b : HilbertBasis ι ℂ H) : Prop :=
  ∀ phi psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ, IsState phi → IsState psi →
    (∀ a, IsDiagonal b a → phi a = psi a) →
    (∀ a a', IsDiagonal b a → IsDiagonal b a' → phi (a * a') = phi a * phi a') →
    phi = psi

/-- **Kadison–Singer, atomic case.** Let `b` be an orthonormal (Hilbert) basis of a Hilbert
space `H` and let `k` be an index. The functional `a ↦ ⟪b k, a (b k)⟫`, restricted to the atomic
MASA of operators that are diagonal with respect to `b`, is a pure state of that MASA (an
*atomic* pure state, i.e. one given by a point of the spectrum that is an atom). Then any state
of `B(H)` extending it is uniquely determined: it is the vector state at `b k`. In particular
any two extensions coincide.

This is the classical "easy half" of the Kadison–Singer problem. The theorem of Marcus, Spielman
and Srivastava extends the conclusion to *all* pure states of the MASA, including the non-atomic
ones coming from free ultrafilters; see `Frontier.KadisonSingerUniqueExtension`. -/
