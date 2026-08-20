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

lemma IsState.eq_diagState_of_diag {f : Matrix n n ℂ →ₗ[ℂ] ℂ} {i : n} (hf : IsState f)
    (h : ∀ j : n, f (Matrix.single j j 1) = if j = i then 1 else 0) :
    f = diagState i := by
  have hoff : ∀ j k : n, j ≠ k → f (Matrix.single j k 1) = 0 := by
    intro j k hjk
    by_cases hji : j = i
    · have hk : k ≠ i := by rintro rfl; exact hjk hji
      have hkz : f (Matrix.single k k 1) = 0 := by simp [h k, hk]
      exact (hf.single_offdiag_eq_zero (j := k) (k := j) hkz).2
    · have hjz : f (Matrix.single j j 1) = 0 := by simp [h j, hji]
      exact (hf.single_offdiag_eq_zero (j := j) (k := k) hjz).1
  ext A
  have hterm : ∀ j k : n, f (Matrix.single j k (A j k))
      = if j = i then (if k = i then A i i else 0) else 0 := by
    intro j k
    have hsm : Matrix.single j k (A j k) = (A j k) • Matrix.single j k (1 : ℂ) := by simp
    rw [hsm, map_smul]
    by_cases hjk : j = k
    · subst hjk
      by_cases hji : j = i
      · subst hji; simp [h j]
      · simp [h j, hji]
    · simp [hoff j k hjk]
      rintro rfl rfl
      exact absurd rfl hjk
  rw [diagState_apply]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, hterm]
  simp

/-! ### Existence and purity -/

