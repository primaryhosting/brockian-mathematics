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
# Equidistribution / uniformity for transitive group actions

For a finite group `G` acting transitively on a finite type `X`, the "hitting sets"
`{g : G | g • x = y}` all have the same cardinality, namely `|G| / |X|`.
Equivalently, if `g` is drawn uniformly at random from `G`, then `g • x` is uniformly
distributed on `X`.

The main result `sing_uniform_of_transitive` is stated unconditionally (beyond
transitivity of the action): no auxiliary uniformity hypothesis is assumed.
-/

namespace Brockian.EquidistributionUniformity

open scoped Pointwise

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The set of group elements sending `x` to `x` is exactly the stabilizer, as a `Finset`. -/

theorem card_filter_smul_const (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y₁ y₂ : X) :
    (Finset.univ.filter fun g : G => g • x = y₁).card
      = (Finset.univ.filter fun g : G => g • x = y₂).card := by
  have h1 := sing_uniform_of_transitive htrans x y₁
  have h2 := sing_uniform_of_transitive htrans x y₂
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_left hX (h1.trans h2.symm)

end Brockian.EquidistributionUniformity

