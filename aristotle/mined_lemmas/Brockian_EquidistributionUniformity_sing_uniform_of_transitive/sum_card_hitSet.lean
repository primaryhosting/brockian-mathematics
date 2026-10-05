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
