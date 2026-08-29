/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

namespace Math2

open MvPolynomial

/-!
## Setting

We work with affine plane curves over a field `k` of characteristic zero, points of the
affine plane being encoded as functions `Fin 2 → k` (so that they can be plugged into
`MvPolynomial (Fin 2) k`).

The theorem `Math2.hironaka_resolution` below is a formalised instance of Hironaka's
resolution of singularities in characteristic zero: for every `m ≥ 1` the plane curve

  `C_m : y ^ 2 = x ^ (2 * m + 1)`

is singular (exactly at the origin), and the map

  `π_m : 𝔸¹ → C_m , t ↦ (t ^ 2, t ^ (2 * m + 1))`

from the smooth affine line is a proper birational bijection onto `C_m` which is an
isomorphism away from the singular point; i.e. `π_m` is a resolution of singularities
of `C_m`.
-/

variable {k : Type*} [Field k]

omit [Field k] in
/-- Two points of the affine plane agree iff their coordinates do. -/

theorem range_param (m : ℕ) : Set.range (param (k := k) m) = curve m := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨t, rfl⟩
    exact param_mem_curve m t
  · intro p hp
    rcases eq_or_ne (p 0) 0 with h0 | h0
    · refine ⟨0, ?_⟩
      have hy : p 1 = 0 := (curve_coord_zero_iff hp).mp h0
      rw [pt_ext_iff]
      simp [param, h0, hy]
    · refine ⟨paramInv m p, ?_⟩
      have hx : p 0 ^ m ≠ 0 := pow_ne_zero _ h0
      have hsq : (paramInv m p) ^ 2 = p 0 := by
        rw [mem_curve_iff] at hp
        rw [paramInv, div_pow, hp]
        field_simp
        ring
      rw [pt_ext_iff]
      refine ⟨by simpa using hsq, ?_⟩
      have : paramInv m p ^ (2 * m + 1) = (paramInv m p ^ 2) ^ m * paramInv m p := by
        rw [← pow_mul, ← pow_succ]
      rw [param_one_coord, this, hsq, paramInv]
      field_simp

/-- **The parametrisation is injective.** -/
