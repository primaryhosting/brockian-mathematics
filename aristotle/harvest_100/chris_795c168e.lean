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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

/-- A weight function that is invariant under a transitively acting symmetry group is
constant. -/
theorem const_of_transitive_symmetry {X : Type*} {G : Type*} [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution from transitive symmetry.**
If a finite set `X` carries a transitive action of a symmetry group `G`, and `w : X → ℝ`
is a `G`-invariant weight of total mass `1`, then `w` is the uniform distribution:
`w x = 1 / |X|` for every `x`.

This is unconditional: no nonemptiness assumption is needed, since the normalization
`∑ x, w x = 1` already rules out the empty case. -/
theorem equidistribution_of_transitive_symmetry {X : Type*} [Fintype X] {G : Type*} [Group G]
    [MulAction G X] (htrans : ∀ x y : X, ∃ g : G, g • x = y) (w : X → ℝ)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) (hsum : ∑ x : X, w x = 1) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) := by
  intro x
  have hconst : ∀ y : X, w y = w x := fun y =>
    const_of_transitive_symmetry htrans w hinv y x
  have hcard : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y)]
    simp [Finset.sum_const, Fintype.card, mul_comm]
  have hne : (Fintype.card X : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcard
    exact zero_ne_one hcard
  field_simp
  linarith [hcard]

end EquidistributionUniformity
end Brockian

