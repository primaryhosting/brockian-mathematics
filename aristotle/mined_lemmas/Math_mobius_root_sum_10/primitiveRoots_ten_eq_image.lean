/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The set of primitive `10`-th roots of unity in `ℂ` is `{ζ, ζ³, ζ⁷, ζ⁹}` for any
primitive `10`-th root of unity `ζ`. -/

theorem primitiveRoots_ten_eq_image {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 10) :
    primitiveRoots 10 ℂ = ({1, 3, 7, 9} : Finset ℕ).image (ζ ^ ·) := by
  ext x
  rw [mem_primitiveRoots (by norm_num), hζ.isPrimitiveRoot_iff]
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, hcop, rfl⟩
    refine ⟨i, ?_, rfl⟩
    interval_cases i <;> revert hcop <;> decide
  · rintro ⟨i, hi, rfl⟩
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨_, by norm_num, by decide, rfl⟩

/-- For a primitive `10`-th root of unity `ζ`, the sum `ζ + ζ³ + ζ⁷ + ζ⁹` equals `1`
(it is minus the coefficient of `X³` in the tenth cyclotomic polynomial
`X⁴ - X³ + X² - X + 1`). -/
