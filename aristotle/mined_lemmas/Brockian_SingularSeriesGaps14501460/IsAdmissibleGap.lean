import Mathlib

set_option maxHeartbeats 200000

example (r : ZMod 2) (h0 : (0 : ZMod 2) ≠ r) (h1 : (1 : ZMod 2) ≠ r) : False := by
  fin_cases r <;> simp_all

example : ({2, 5, 29} : Finset ℕ).erase 2 = {5, 29} := by
  rw [Finset.erase_insert (by simp)]

example : (∏ p ∈ ({5, 29} : Finset ℕ), (((p : ℚ) - 1) / ((p : ℚ) - 2))) = 112 / 81 := by
  rw [Finset.prod_insert (by simp), Finset.prod_singleton]
  norm_num

example (g : ℕ) (hmod : g % 2 = 1) : (((g : ℤ)) : ZMod 2) = 1 := by
  push_cast
  rw [← ZMod.natCast_mod g 2, hmod]
  norm_num

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood
prime constellations) if for every prime `p` the reductions of the elements of `H`
mod `p` do not cover all residue classes mod `p`. -/

def IsAdmissibleGap (g : ℕ) : Prop := IsAdmissibleSet {0, (g : ℤ)}

/-- The odd part of the Hardy–Littlewood singular series for the pair `{0, g}`:
`∏_{p ∣ g, p odd prime} (p-1)/(p-2)`.  (The full singular series is
`2 C₂` times this factor.) -/
