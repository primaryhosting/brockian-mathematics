/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A Bhargava cube: a `2 × 2 × 2` array of integers.  We label the eight entries as in
Bhargava's *Higher composition laws I*: the front face is `a b / c d` and the back face is
`e f / g h`. -/
structure Cube where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
  deriving DecidableEq

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure QF where
  A : ℤ
  B : ℤ
  C : ℤ
  deriving DecidableEq

namespace QF

/-- Evaluation of a binary quadratic form. -/

theorem bhargava_cube_law :
    (∀ K : Cube, K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc) ∧
    (∀ A₁ A₂ B C : ℤ,
      (concordantCube A₁ A₂ B C).Q₁ = ⟨A₁, B, A₂ * C⟩ ∧
      (concordantCube A₁ A₂ B C).Q₂ = ⟨A₂, B, A₁ * C⟩ ∧
      (concordantCube A₁ A₂ B C).Q₃.op = ⟨A₁ * A₂, B, C⟩ ∧
      ∀ x₁ y₁ x₂ y₂ : ℤ,
        (concordantCube A₁ A₂ B C).Q₁.eval x₁ y₁ *
            (concordantCube A₁ A₂ B C).Q₂.eval x₂ y₂ =
          (concordantCube A₁ A₂ B C).Q₃.op.eval (x₁ * x₂ - C * y₁ * y₂)
            (A₁ * x₁ * y₂ + A₂ * x₂ * y₁ + B * y₁ * y₂)) := by
  refine ⟨disc_eq, fun A₁ A₂ B C => ?_⟩
  have h₁ : (concordantCube A₁ A₂ B C).Q₁ = ⟨A₁, B, A₂ * C⟩ := by
    simp [concordantCube, Cube.Q₁]
  have h₂ : (concordantCube A₁ A₂ B C).Q₂ = ⟨A₂, B, A₁ * C⟩ := by
    simp [concordantCube, Cube.Q₂]
  have h₃ : (concordantCube A₁ A₂ B C).Q₃.op = ⟨A₁ * A₂, B, C⟩ := by
    simp [concordantCube, Cube.Q₃, QF.op]
  refine ⟨h₁, h₂, h₃, fun x₁ y₁ x₂ y₂ => ?_⟩
  rw [h₁, h₂, h₃]
  exact concordant_compose A₁ A₂ B C x₁ y₁ x₂ y₂

end Frontier

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

