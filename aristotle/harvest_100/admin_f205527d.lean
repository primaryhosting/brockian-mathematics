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
/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The sum of the primitive `k`-th roots of unity, expressed as a sum of powers of a fixed
primitive `k`-th root over the exponents coprime to `k`. -/
theorem sum_primitiveRoots_eq_sum_pow {ζ : ℂ} {k : ℕ} (h : IsPrimitiveRoot ζ k) (h0 : k ≠ 0) :
    ∑ x ∈ primitiveRoots k ℂ, x = ∑ i ∈ (range k).filter (fun i => k.Coprime i), ζ ^ i := by
  have : NeZero k := ⟨h0⟩
  symm
  refine Finset.sum_bij (fun i _ ↦ ζ ^ i) ?_ ?_ ?_ ?_
  · simp only [and_imp, mem_filter, mem_range]
    rintro i - hi
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0)]
    exact h.pow_of_coprime i hi.symm
  · simp only [and_imp, mem_filter, mem_range]
    rintro i hi - j hj - H
    exact h.pow_inj hi hj H
  · simp only [exists_prop, mem_filter, mem_range]
    intro ξ hξ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0), h.isPrimitiveRoot_iff] at hξ
    rcases hξ with ⟨i, hin, hi, H⟩
    exact ⟨i, ⟨hin, hi.symm⟩, H⟩
  · intros; rfl

/-- The sum of the primitive `5`-th roots of unity equals `μ 5 = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hgeom : ∑ i ∈ range 5, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hfilter : (range 5).filter (fun i => Nat.Coprime 5 i) = {1, 2, 3, 4} := by decide
  rw [sum_primitiveRoots_eq_sum_pow hζ (by norm_num), hfilter,
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hgeom
  norm_num [Finset.sum_insert, Finset.mem_insert] at hgeom ⊢
  linear_combination hgeom

end Math

