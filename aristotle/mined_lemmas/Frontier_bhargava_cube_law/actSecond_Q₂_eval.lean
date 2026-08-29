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

namespace Frontier

/-- An integral binary quadratic form `A x ^ 2 + B x y + C y ^ 2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : ℤ
  B : ℤ
  C : ℤ
deriving DecidableEq

namespace BQF

/-- The discriminant `B ^ 2 - 4 A C` of a binary quadratic form. -/

lemma actSecond_Q₂_eval (K : Cube) (p q r s x y : ℤ) :
    (K.actSecond p q r s).Q₂.eval x y = K.Q₂.eval (p * x + r * y) (q * x + s * y) := by
  simp only [actSecond, Q₂, BQF.eval]; ring

