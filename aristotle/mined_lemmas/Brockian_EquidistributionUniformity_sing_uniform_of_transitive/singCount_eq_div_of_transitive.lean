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

theorem singCount_eq_div_of_transitive [Finite G] [IsPretransitive G X] (x y : X) :
    singCount G x y = Nat.card G / Nat.card X := by
  have h := (sing_uniform_of_transitive (G := G) x y x y).2
  have hX : 0 < Nat.card X := Nat.card_pos_iff.2 ⟨⟨x⟩, Finite.of_surjective
    (fun g : G => g • x) (fun z => MulAction.exists_smul_eq G x z)⟩
  rw [← h, Nat.mul_div_cancel _ hX]

/-! ### Sanity checks: the hypotheses are satisfiable and the counts are the expected ones. -/

/-- The hypothesis of transitivity is satisfiable: the symmetric group acts transitively. -/
example : MulAction.IsPretransitive (Equiv.Perm (Fin 3)) (Fin 3) := inferInstance

/-- For the left regular action of a group on itself the uniform count is `1`. -/
example (G : Type*) [Group G] (x y : G) : singCount G x y = 1 := by
  have h : transportSet G x y = {y * x⁻¹} := by
    ext g
    simp only [transportSet, Set.mem_setOf_eq, smul_eq_mul, Set.mem_singleton_iff,
      eq_mul_inv_iff_mul_eq]
  rw [singCount, h, Nat.card_coe_set_eq, Set.ncard_singleton]


end EquidistributionUniformity
end Brockian

