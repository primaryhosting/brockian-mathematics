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
# Mobius Root Sum 9
Category: Pure Mathematics
Target: Math.mobius_root_sum_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of primitive `n`-th roots of unity is the image of the exponents in `[0, n)` that are
coprime to `n` under `k ↦ ζ ^ k`, for any primitive `n`-th root of unity `ζ`. -/
theorem primitiveRoots_eq_image_pow {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}
    {ζ : R} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    primitiveRoots n R = ((range n).filter fun k => Nat.gcd k n = 1).image fun k => ζ ^ k := by
  have : NeZero n := ⟨hn.ne'⟩
  ext x
  simp only [mem_primitiveRoots hn, mem_image, mem_filter, mem_range]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one (ξ := x) hx.pow_eq_one
    have hix' : ζ ^ (i % n) = x := by
      rw [← pow_mod_orderOf, ← hζ.eq_orderOf] at hix; exact hix
    refine ⟨i % n, ⟨Nat.mod_lt _ hn, ?_⟩, hix'⟩
    have h2 : IsPrimitiveRoot (ζ ^ (i % n)) n := by rw [hix']; exact hx
    exact (hζ.pow_iff_coprime hn (i % n)).mp h2
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact hζ.pow_of_coprime i hi

/-- The sum of the primitive `9`-th roots of unity in `ℂ` equals `μ 9` (which is `0`). -/
theorem mobius_root_sum_9 :
    ∑ z ∈ primitiveRoots 9 ℂ, z = ((ArithmeticFunction.moebius 9 : ℤ) : ℂ) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 9 := ⟨_, Complex.isPrimitiveRoot_exp 9 (by norm_num)⟩
  have hsum9 : ∑ i ∈ range 9, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hζ3 : IsPrimitiveRoot (ζ ^ 3) 3 := hζ.pow (by norm_num) (by norm_num)
  have hsum3 : ∑ i ∈ range 3, (ζ ^ 3) ^ i = 0 := hζ3.geom_sum_eq_zero (by norm_num)
  have hmu : ArithmeticFunction.moebius 9 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun h => by simpa [Nat.isUnit_iff] using h 3 ⟨1, by norm_num⟩)
  have h1 : ((range 9).filter fun k => Nat.gcd k 9 = 1) = {1, 2, 4, 5, 7, 8} := by decide
  rw [primitiveRoots_eq_image_pow (by norm_num) hζ, Finset.sum_image, h1, hmu]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero] at hsum9 hsum3
    norm_num
    linear_combination hsum9 - hsum3
  · intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_range] at ha hb
    exact hζ.pow_inj ha.1 hb.1 hab

end Math

