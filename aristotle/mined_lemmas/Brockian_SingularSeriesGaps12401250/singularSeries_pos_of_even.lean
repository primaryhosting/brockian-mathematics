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

/-- A finite set of integers is *admissible* (in the sense of the prime `k`-tuples
conjecture) if for every prime `p` it fails to cover all residue classes modulo `p`. -/

theorem singularSeries_pos_of_even {h : ℕ} (he : Even h) (hh : h ≠ 0) :
    0 < singularSeries h := by
  rw [singularSeries, if_pos ⟨he, hh⟩]
  refine Finset.prod_pos ?_
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpp, _, _⟩, hp2⟩ := hp
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  apply div_pos <;> linarith

/-- The singular series vanishes for odd gaps. -/
