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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The set of coprime residues mod `9` in `range 9`. -/

lemma sum_pow_primitive_nine {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) :
    ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime 9 i), ζ ^ i = 0 := by
  have h9 : ζ ^ 9 = 1 := hζ.pow_eq_one
  have h3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 3 - 1) * (ζ ^ 6 + ζ ^ 3 + 1) = 0 := by linear_combination h9
  have hsum : ζ ^ 6 + ζ ^ 3 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact h
  rw [coprime_filter_nine]
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination (ζ + ζ ^ 2) * hsum

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ 9`. -/
