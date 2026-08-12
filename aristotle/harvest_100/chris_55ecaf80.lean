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

(Note: the header is a plain block comment rather than a module docstring, because in Lean 4 a
module docstring may not appear before the `import` line.)
-/

import Mathlib

namespace Brockian
namespace EquidistributionUniformity

/-- A real-valued weight function invariant under a transitive group action is constant. -/
theorem const_of_transitive_invariant {G X : Type*} [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution of transitive symmetry.**
If a group `G` acts transitively on a finite type `X` and `w : X → ℝ` is a `G`-invariant
weight summing to `1`, then `w` is the uniform distribution: `w x = 1 / |X|` for every `x`.
No uniformity hypothesis is assumed; it is derived from transitivity and invariance. -/
theorem equidistribution_of_transitive_symmetry {G X : Type*} [Group G] [Fintype X]
    [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x, w x = 1) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) := by
  intro x
  have hconst : ∀ y : X, w y = w x := fun y =>
    const_of_transitive_invariant htrans w hinv y x
  have hcard : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y)]
    simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have hne : (Fintype.card X : ℝ) ≠ 0 := by
    intro h
    rw [h] at hcard
    simp at hcard
  field_simp
  linarith [hcard]

/-- Mathlib-idiomatic restatement: the transitivity hypothesis is packaged as the typeclass
`MulAction.IsPretransitive G X`, from which `MulAction.exists_smul_eq` supplies the group
element moving one point to another. -/
theorem equidistribution_of_isPretransitive {G X : Type*} [Group G] [Fintype X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x, w x = 1) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) :=
  equidistribution_of_transitive_symmetry
    (fun x y => MulAction.exists_smul_eq G x y) w hinv hsum

end EquidistributionUniformity
end Brockian

