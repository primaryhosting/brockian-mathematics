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

namespace Brockian
namespace EquidistributionUniformity

open MulAction

/-- The fibre `{g : G | g • a = x}` of the orbit map at `a` over a point `x` in the orbit is
in bijection with the stabilizer of `a`.  (Any such fibre is a left coset of `stabilizer G a`.) -/

theorem sing_uniform_ratio_of_transitive {G α : Type*} [Group G] [Finite G] [MulAction G α]
    [IsPretransitive G α] [Nonempty α] (a x : α) :
    (Nat.card {g : G // g • a = x} : ℝ) / Nat.card G = 1 / Nat.card α := by
  haveI : Finite α := Finite.of_surjective (fun g : G => g • a) (fun y => exists_smul_eq G a y)
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hα : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  have h' : (Nat.card {g : G // g • a = x} : ℝ) * (Nat.card α : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast sing_uniform_of_transitive (G := G) a x
  field_simp
  linarith [h']

end EquidistributionUniformity
end Brockian

