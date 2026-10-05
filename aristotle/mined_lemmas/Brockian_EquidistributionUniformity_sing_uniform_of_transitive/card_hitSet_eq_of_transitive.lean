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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian.EquidistributionUniformity

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

/-- The fibre of the orbit map `g ↦ g • x` over a point `y`. -/

theorem card_hitSet_eq_of_transitive (htrans : ∀ y z : X, ∃ g : G, g • y = z)
    (x y z : X) : (hitSet (G := G) x y).card = (hitSet (G := G) x z).card := by
  obtain ⟨a, ha⟩ := htrans y z
  refine Finset.card_bij' (fun g _ => a * g) (fun g _ => a⁻¹ * g) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ha]
  · intro g hg
    simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ← ha, inv_smul_smul]
  · intro g _; simp
  · intro g _; simp

/-- The fibres of the orbit map `g ↦ g • x` partition the group. -/
