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

namespace Brockian
namespace EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The *singular transport set* of the pair `(x, y)`: the set of group elements that move the
point `x` to the point `y`. -/

lemma singCount_eq_card_stabilizer [IsPretransitive G X] (x y : X) :
    singCount G x y = Nat.card (stabilizer G x) := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  exact Nat.card_congr (transportSet_equiv_stabilizer hg₀).some

/-- **Equidistribution uniformity for transitive actions.**

If a group `G` acts transitively on `X`, then the number of group elements carrying a given point
`x` to a given point `y` does not depend on the chosen pair `(x, y)` (uniformity), and this common
count multiplied by the number of points of `X` is the order of `G`.

In particular, for finite `G` and `X` the count is exactly `|G| / |X|`. -/
