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
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

open MulAction

/-- The set of group elements moving `x` to `y` is a left coset of the stabilizer of `x`,
hence has the same cardinality as the stabilizer, provided some element does move `x` to `y`. -/

theorem sing_uniform_of_forall_exists_smul_eq {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype X] [DecidableEq X] (htrans : ∀ a b : X, ∃ g : G, g • a = b) (x y : X) :
    (Finset.univ.filter fun g : G => g • x = y).card * Fintype.card X = Fintype.card G := by
  haveI : MulAction.IsPretransitive G X := ⟨fun a b => htrans a b⟩
  exact sing_uniform_of_transitive x y

end EquidistributionUniformity
end Brockian

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

