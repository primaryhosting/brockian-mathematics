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

/-- The sum of the primitive `5`-th roots of unity in `ℂ` equals `μ(5) = -1`.

The proof identifies `primitiveRoots 5 ℂ` with `{ζ, ζ², ζ³, ζ⁴}` for a primitive root `ζ`
(existence from `Complex.isPrimitiveRoot_exp`), uses `Complex.card_primitiveRoots` together
with `Nat.totient_prime` for the cardinality, and concludes with
`IsPrimitiveRoot.geom_sum_eq_zero` (`1 + ζ + ζ² + ζ³ + ζ⁴ = 0`) and
`ArithmeticFunction.moebius_apply_prime`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 :=
    ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) ({1, 2, 3, 4} : Finset ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hi hj
    have hi5 : i < 5 := by rcases hi with h | h | h | h <;> omega
    have hj5 : j < 5 := by rcases hj with h | h | h | h <;> omega
    exact hζ.pow_inj hi5 hj5 hij
  have himg : primitiveRoots 5 ℂ = ({1, 2, 3, 4} : Finset ℕ).image (fun i => ζ ^ i) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [mem_primitiveRoots (by norm_num)] at hx
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx.pow_eq_one
      simp only [Finset.mem_image]
      refine ⟨i, ?_, rfl⟩
      interval_cases i
      · exact absurd (by simp : ((ζ ^ 0) ^ 1 : ℂ) = 1)
          (hx.pow_ne_one_of_pos_of_lt one_ne_zero (by norm_num))
      all_goals simp
    · rw [Complex.card_primitiveRoots, Nat.totient_prime (by norm_num),
        Finset.card_image_of_injOn hinj]
      decide
  rw [himg, Finset.sum_image (fun i hi j hj h => hinj hi hj h)]
  have h0 : ∑ i ∈ Finset.range 5, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num)]
  simp [Finset.sum_range_succ] at h0 ⊢
  linear_combination h0

end Math

