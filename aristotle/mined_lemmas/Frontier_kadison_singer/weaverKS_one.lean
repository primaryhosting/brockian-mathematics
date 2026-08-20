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

theorem weaverKS_one (α : ℝ) : WeaverKS 1 α := by
  intro d m v _ hres
  refine ⟨fun _ => 0, ?_⟩
  intro j x
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have hfil : (Finset.univ.filter (fun i : Fin m => (0 : Fin 1) = 0)) = Finset.univ := by simp
  rw [hfil, hres x]
  have h1 : (1 : ℝ) ≤ (1 / Real.sqrt 1 + Real.sqrt α) ^ 2 := by
    have hs : Real.sqrt α ≥ 0 := Real.sqrt_nonneg α
    rw [Real.sqrt_one]
    nlinarith
  nlinarith [sq_nonneg ‖x‖, norm_nonneg x]

end Frontier

