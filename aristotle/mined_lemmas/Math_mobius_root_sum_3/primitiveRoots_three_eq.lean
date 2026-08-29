/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset ArithmeticFunction ArithmeticFunction.Moebius

/-- `ζ = exp (2 π i / 3)` is a primitive cube root of unity. -/

theorem primitiveRoots_three_eq :
    primitiveRoots 3 ℂ = {Complex.exp (2 * Real.pi * Complex.I / 3),
      Complex.exp (2 * Real.pi * Complex.I / 3) ^ 2} := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := isPrimitiveRoot_exp_three
  have hne : ζ ≠ ζ ^ 2 := exp_three_ne_sq
  have hsub : ({ζ, ζ ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hζ
    · exact (mem_primitiveRoots (by norm_num)).2 (hζ.pow_of_coprime 2 (by decide))
  have hcard : (primitiveRoots 3 ℂ).card = 2 := by
    rw [hζ.card_primitiveRoots]; decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ 3`. -/
