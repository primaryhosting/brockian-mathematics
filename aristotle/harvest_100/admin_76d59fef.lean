/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module doc comment `/-! ... -/`, so the header above
-- is written as an ordinary block comment; it is repeated verbatim as a doc comment below.)

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

/-- The sum of the primitive `10`-th roots of unity in `ℂ` equals `μ(10) = 1`.

The primitive 10-th roots are `ζ, ζ³, ζ⁷, ζ⁹` for `ζ = exp(2πi/10)`; using `ζ⁵ = -1` and
`ζ ≠ -1` one gets `(ζ + 1)(ζ + ζ³ + ζ⁷ + ζ⁹ - 1) = 0`, hence the sum is `1`.

Relevant Mathlib ingredients: `Complex.isPrimitiveRoot_exp`, `Complex.card_primitiveRoots`,
`mem_primitiveRoots`, `IsPrimitiveRoot.pow_of_coprime`, `IsPrimitiveRoot.pow_inj`. -/
theorem mobius_root_sum_10 :
    ∑ x ∈ primitiveRoots 10 ℂ, x = ((ArithmeticFunction.moebius 10 : ℤ) : ℂ) := by
  have hz := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10) with hzdef
  -- distinctness of the relevant powers of `z`
  have hne : ∀ i j : ℕ, i < 10 → j < 10 → i ≠ j → z ^ i ≠ z ^ j :=
    fun i j hi hj hij h => hij (hz.pow_inj hi hj h)
  have h13 : z ≠ z ^ 3 := by simpa using hne 1 3 (by norm_num) (by norm_num) (by norm_num)
  have h15 : z ≠ z ^ 5 := by simpa using hne 1 5 (by norm_num) (by norm_num) (by norm_num)
  have h17 : z ≠ z ^ 7 := by simpa using hne 1 7 (by norm_num) (by norm_num) (by norm_num)
  have h19 : z ≠ z ^ 9 := by simpa using hne 1 9 (by norm_num) (by norm_num) (by norm_num)
  have h37 : z ^ 3 ≠ z ^ 7 := hne 3 7 (by norm_num) (by norm_num) (by norm_num)
  have h39 : z ^ 3 ≠ z ^ 9 := hne 3 9 (by norm_num) (by norm_num) (by norm_num)
  have h79 : z ^ 7 ≠ z ^ 9 := hne 7 9 (by norm_num) (by norm_num) (by norm_num)
  -- `z ^ 5 = -1`
  have h5 : z ^ 5 = -1 := by
    have h10 : z ^ 10 = 1 := hz.pow_eq_one
    have key : (z ^ 5 - 1) * (z ^ 5 + 1) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 key with h | h
    · exact absurd (by linear_combination h : z ^ 5 = 1)
        (hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
    · linear_combination h
  -- the four displayed elements are exactly the primitive 10-th roots of unity
  have hsub : ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ) ⊆ primitiveRoots 10 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_primitiveRoots (by norm_num)]
    rcases hx with rfl | rfl | rfl | rfl
    · exact hz
    · exact hz.pow_of_coprime 3 (by norm_num)
    · exact hz.pow_of_coprime 7 (by norm_num)
    · exact hz.pow_of_coprime 9 (by norm_num)
  have hcard : ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h13, h17, h19]),
        Finset.card_insert_of_notMem (by simp [h37, h39]),
        Finset.card_insert_of_notMem (by simp [h79]), Finset.card_singleton]
  have hcard' : (primitiveRoots 10 ℂ).card = 4 := by
    rw [Complex.card_primitiveRoots]
    decide +kernel
  have hset : ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ) = primitiveRoots 10 ℂ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])
  -- compute the sum
  have hsum : ∑ x ∈ ({z, z ^ 3, z ^ 7, z ^ 9} : Finset ℂ), x = z + z ^ 3 + z ^ 7 + z ^ 9 := by
    rw [Finset.sum_insert (by simp [h13, h17, h19]), Finset.sum_insert (by simp [h37, h39]),
        Finset.sum_insert (by simp [h79]), Finset.sum_singleton]
    ring
  have hz1 : z + 1 ≠ 0 := by
    intro h
    exact h15 (by rw [h5]; linear_combination h)
  have hval : z + z ^ 3 + z ^ 7 + z ^ 9 = 1 := by
    have key : (z + 1) * (z + z ^ 3 + z ^ 7 + z ^ 9 - 1) = 0 := by
      linear_combination (z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 - 1) * h5
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hz1
    · linear_combination h
  have hmu : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree (by decide +kernel),
      ArithmeticFunction.cardFactors_apply]
    norm_num [show Nat.primeFactorsList 10 = [2, 5] from by decide +kernel]
  rw [← hset, hsum, hval, hmu]
  norm_num

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

