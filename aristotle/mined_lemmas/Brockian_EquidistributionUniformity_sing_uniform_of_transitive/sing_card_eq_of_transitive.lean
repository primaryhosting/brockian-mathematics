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

import Mathlib

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- For a transitive action, the fiber `{g | g • x = y}` over any point `y` is in bijection
with the stabilizer of `x`: the map `g ↦ g₀⁻¹ * g` (where `g₀ • x = y`) is a bijection from the
fiber onto `stabilizer G x`. -/

theorem sing_card_eq_of_transitive [IsPretransitive G X] [Finite X] [Nonempty X]
    (x y x' y' : X) :
    Nat.card {g : G // g • x = y} = Nat.card {g : G // g • x' = y'} := by
  have hX : (0 : ℕ) < Nat.card X := Nat.card_pos
  have h₁ := sing_uniform_of_transitive (G := G) x y
  have h₂ := sing_uniform_of_transitive (G := G) x' y'
  exact Nat.eq_of_mul_eq_mul_right hX (h₁.trans h₂.symm)

end Brockian.EquidistributionUniformity

