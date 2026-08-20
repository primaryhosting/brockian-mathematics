import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

lemma sum_sq_reflection_solutions (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ((Finset.univ.filter fun x : ZMod n => 2 * x = i).card) ^ 2
      = n * (Finset.univ.filter fun d : ZMod n => 2 * d = 0).card := by
  classical
  have hsq : ∀ i : ZMod n, ((Finset.univ.filter fun x : ZMod n => 2 * x = i).card) ^ 2
      = ∑ x : ZMod n, ∑ y : ZMod n,
          (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0) := by
    intro i
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
  simp only [hsq]
  rw [Finset.sum_comm]
  have step : ∀ x : ZMod n,
      ∑ i : ZMod n, ∑ y : ZMod n, (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0)
        = (Finset.univ.filter fun d : ZMod n => 2 * d = 0).card := by
    intro x
    rw [Finset.sum_comm]
    have hcollapse : ∀ y : ZMod n,
        ∑ i : ZMod n, (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0)
          = if 2 * y = 2 * x then 1 else 0 := by
      intro y
      rw [Finset.sum_eq_single (2 * x)] <;> simp +contextual
      intro b hb _
      simp [Ne.symm hb]
    simp only [hcollapse]
    rw [Finset.card_filter]
    refine (Fintype.sum_equiv (Equiv.addRight x)
      (fun d : ZMod n => if 2 * d = 0 then 1 else 0)
      (fun y : ZMod n => if 2 * y = 2 * x then 1 else 0) ?_).symm
    intro d
    simp only [Equiv.coe_addRight]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  simp only [step]
  simp [ZMod.card]

/-- The sum of the squares of the character values, computed in `ℕ`. -/
