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

open Finset Complex

namespace Math

/-- The set of primitive `9`-th roots of unity in `ℂ`, described as the powers `ζ ^ i`
with `i < 9` coprime to `9`, where `ζ` is a fixed primitive `9`-th root of unity. -/

theorem sum_coprime_pow_nine {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) :
    ∑ i ∈ (Finset.range 9).filter (fun i => Nat.Coprime i 9), ζ ^ i = 0 := by
  have hgeom : ∑ i ∈ Finset.range 9, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hcube : IsPrimitiveRoot (ζ ^ 3) 3 := by
    have := hζ.pow (n := 9) (by norm_num) (b := 3) (by norm_num)
    simpa using this
  have hgeom3 : ∑ i ∈ Finset.range 3, (ζ ^ 3) ^ i = 0 := hcube.geom_sum_eq_zero (by norm_num)
  have h9 : (Finset.range 9).filter (fun i => Nat.Coprime i 9) = ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
    decide
  rw [h9]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hgeom hgeom3
  norm_num [Finset.sum_insert, Finset.mem_insert]
  linear_combination hgeom - hgeom3

/-- **The sum of the primitive 9-th roots of unity equals `μ(9)`.** -/
