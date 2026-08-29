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
def hitSet (x y : X) : Finset G := Finset.univ.filter (fun g : G => g • x = y)

omit [Fintype X] in
/-- For a transitive action, all fibres of the orbit map `g ↦ g • x` have the same
cardinality. -/
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
theorem sum_card_hitSet (x : X) :
    ∑ y : X, (hitSet (G := G) x y).card = Fintype.card G := by
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
    (f := fun g : G => g • x) (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  rfl

/-- **Uniformity of a transitive action on singletons.** If a finite group `G` acts
transitively on a finite type `X`, then for every base point `x` and every target point
`y` the set of group elements sending `x` to `y` has cardinality exactly
`|G| / |X|`; equivalently, its cardinality times `|X|` equals `|G|`.  Thus the
push-forward of the uniform distribution on `G` under `g ↦ g • x` is the uniform
distribution on `X`. -/
theorem sing_uniform_of_transitive (htrans : ∀ y z : X, ∃ g : G, g • y = z)
    (x y : X) : (hitSet (G := G) x y).card * Fintype.card X = Fintype.card G := by
  rw [← sum_card_hitSet (G := G) x]
  rw [Finset.sum_congr rfl (fun z _ => card_hitSet_eq_of_transitive htrans x z y)]
  rw [Finset.sum_const, smul_eq_mul, Fintype.card, mul_comm]

end Brockian.EquidistributionUniformity

#print axioms Brockian.EquidistributionUniformity.sing_uniform_of_transitive

