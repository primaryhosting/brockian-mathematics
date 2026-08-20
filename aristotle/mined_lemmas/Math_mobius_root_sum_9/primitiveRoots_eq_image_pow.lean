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
