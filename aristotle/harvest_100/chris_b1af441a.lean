/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The sum of the primitive `k`-th roots of unity, expressed as a sum of powers of a
fixed primitive `k`-th root. -/
theorem sum_primitiveRoots_eq_sum_pow {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) :
    ∑ z ∈ primitiveRoots k ℂ, z
      = ∑ i ∈ (Finset.range k).filter (fun i => Nat.Coprime k i), ζ ^ i := by
  haveI : NeZero k := ⟨hk⟩
  symm
  refine Finset.sum_bij (fun i _ => ζ ^ i) ?_ ?_ ?_ ?_
  · simp only [and_imp, mem_filter, mem_range]
    rintro i - hi
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero hk)]
    exact hζ.pow_of_coprime i hi.symm
  · simp only [and_imp, mem_filter, mem_range]
    rintro i hi - j hj - H
    exact hζ.pow_inj hi hj H
  · simp only [exists_prop, mem_filter, mem_range]
    intro ξ hξ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero hk), hζ.isPrimitiveRoot_iff] at hξ
    rcases hξ with ⟨i, hin, hi, H⟩
    exact ⟨i, ⟨hin, hi.symm⟩, H⟩
  · intro i _
    rfl

/-- A primitive `8`-th root of unity satisfies `ζ ^ 4 = -1`. -/
theorem pow_four_eq_neg_one_of_isPrimitiveRoot_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 8) :
    ζ ^ 4 = -1 := by
  have h8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  have h4 : ζ ^ 4 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hprod : (ζ ^ 4 - 1) * (ζ ^ 4 + 1) = 0 := by linear_combination h8
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (by linear_combination h) h4
  · linear_combination h

/-- The sum of the primitive `8`-th roots of unity equals `μ 8` (which is `0`, since `8` is not
squarefree). -/
theorem mobius_root_sum_8 :
    ∑ z ∈ primitiveRoots 8 ℂ, z = (ArithmeticFunction.moebius 8 : ℂ) := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 8)) 8 :=
    Complex.isPrimitiveRoot_exp 8 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8) with hζdef
  have hsum := sum_primitiveRoots_eq_sum_pow (k := 8) (by norm_num) hζ
  have hfilter :
      (Finset.range 8).filter (fun i => Nat.Coprime 8 i) = ({1, 3, 5, 7} : Finset ℕ) := by
    decide
  have hmu : (ArithmeticFunction.moebius 8 : ℂ) = 0 := by
    have h : ArithmeticFunction.moebius 8 = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
    rw [h]
    norm_num
  have h4 : ζ ^ 4 = -1 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight hζ
  have h5 : ζ ^ 5 = -(ζ ^ 1) := by
    have h : ζ ^ 5 = ζ ^ 4 * ζ ^ 1 := by ring
    rw [h, h4]; ring
  have h7 : ζ ^ 7 = -(ζ ^ 3) := by
    have h : ζ ^ 7 = ζ ^ 4 * ζ ^ 3 := by ring
    rw [h, h4]; ring
  rw [hsum, hfilter, hmu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h5, h7]
  ring

end Math

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

