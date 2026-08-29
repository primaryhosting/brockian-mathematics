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
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The set of primitive `5`-th roots of unity in `ℂ` is `{ζ, ζ², ζ³, ζ⁴}` for
`ζ` a primitive `5`-th root of unity. -/
lemma primitiveRoots_five_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    primitiveRoots 5 ℂ = {ζ, ζ ^ 2, ζ ^ 3, ζ ^ 4} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have hx' : IsPrimitiveRoot x 5 := (mem_primitiveRoots (by norm_num)).mp hx
    obtain ⟨i, hi, hcop, rfl⟩ := (hζ.isPrimitiveRoot_iff).mp hx'
    interval_cases i <;> simp_all [Nat.Coprime]
  · rw [Complex.card_primitiveRoots]
    have h5 : Nat.totient 5 = 4 := by decide
    rw [h5]
    have h1 := Finset.card_insert_le ζ ({ζ ^ 2, ζ ^ 3, ζ ^ 4} : Finset ℂ)
    have h2 := Finset.card_insert_le (ζ ^ 2) ({ζ ^ 3, ζ ^ 4} : Finset ℂ)
    have h3 := Finset.card_insert_le (ζ ^ 3) ({ζ ^ 4} : Finset ℂ)
    simp only [Finset.card_singleton] at h3
    omega

/-- The sum of the primitive `5`-th roots of unity equals `μ(5) = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = (ArithmeticFunction.moebius 5 : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / 5), Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  rw [primitiveRoots_five_eq hζ]
  have key : ∀ i j : ℕ, i < 5 → j < 5 → ζ ^ i = ζ ^ j → i = j :=
    fun _ _ hi hj h => hζ.pow_inj hi hj h
  have h12 : ζ ≠ ζ ^ 2 := fun h => by simpa using key 1 2 (by norm_num) (by norm_num) (by simpa using h)
  have h13 : ζ ≠ ζ ^ 3 := fun h => by simpa using key 1 3 (by norm_num) (by norm_num) (by simpa using h)
  have h14 : ζ ≠ ζ ^ 4 := fun h => by simpa using key 1 4 (by norm_num) (by norm_num) (by simpa using h)
  have h23 : ζ ^ 2 ≠ ζ ^ 3 := fun h => by simpa using key 2 3 (by norm_num) (by norm_num) h
  have h24 : ζ ^ 2 ≠ ζ ^ 4 := fun h => by simpa using key 2 4 (by norm_num) (by norm_num) h
  have h34 : ζ ^ 3 ≠ ζ ^ 4 := fun h => by simpa using key 3 4 (by norm_num) (by norm_num) h
  rw [Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
  have hgeom : ∑ i ∈ Finset.range 5, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at hgeom
  have : (ArithmeticFunction.moebius 5 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [show ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) by rw [this]]
  push_cast
  linear_combination hgeom

end Math

