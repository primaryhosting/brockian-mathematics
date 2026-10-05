/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem demoLoc_localStructure : LocalStructure demoLoc := by
  constructor
  · intro S T hST x hx
    by_cases h0 : (0 : ℤ) ∈ S
    · simp [demoLoc, hST h0]
    · simp only [demoLoc, if_neg h0] at hx
      by_cases h1 : (0 : ℤ) ∈ T
      · simp [demoLoc, h1]
      · simpa [demoLoc, if_neg h1] using hx
  · intro S x hx y hy
    by_cases h0 : (0 : ℤ) ∈ S
    · simp [demoLoc, h0]
    · simp only [demoLoc, if_neg h0] at hx hy ⊢
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c * d, by rw [smul_mul_smul_comm, mul_one, mul_smul]⟩
  · intro S T hST x hx y hy
    by_cases h0 : (0 : ℤ) ∈ S
    · have h1 : (0 : ℤ) ∉ T := fun h => (Set.disjoint_left.mp hST h0) h
      simp only [demoLoc, if_neg h1] at hy
      obtain ⟨d, rfl⟩ := hy
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    · simp only [demoLoc, if_neg h0] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- The hypotheses of the Lieb–Robinson bound are consistent, and the locality structure used
can be genuinely noncommutative. -/
