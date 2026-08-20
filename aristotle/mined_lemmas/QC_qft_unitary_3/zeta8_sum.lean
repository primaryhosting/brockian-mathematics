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

namespace QC

open Complex

/-- The primitive 8-th root of unity raised to an integer power `d`,
written as `exp (2 π i d / 8)`. -/

lemma zeta8_sum (d : ℤ) :
    ∑ n : Fin 8, zeta8 ((n : ℤ) * d) = if (8 : ℤ) ∣ d then 8 else 0 := by
  by_cases hd : (8 : ℤ) ∣ d
  · simp only [hd, if_true]
    have h1 : ∀ n : Fin 8, zeta8 ((n : ℤ) * d) = 1 := by
      intro n
      rw [← zeta8_pow d (n : ℕ)]
      · rw [(zeta8_eq_one_iff d).mpr hd, one_pow]
    simp [h1]
  · simp only [hd, if_false]
    have hz : zeta8 d ≠ 1 := fun h => hd ((zeta8_eq_one_iff d).mp h)
    have h8 : zeta8 d ^ 8 = 1 := by
      rw [zeta8_pow]
      exact (zeta8_eq_one_iff _).mpr ⟨d, by push_cast; ring⟩
    have hsum : ∑ n : Fin 8, zeta8 ((n : ℤ) * d) = ∑ i ∈ Finset.range 8, zeta8 d ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => zeta8 ((i : ℤ) * d))]
      · refine Finset.sum_congr rfl ?_
        intro i _
        rw [zeta8_pow]
    rw [hsum, geom_sum_eq hz, h8]
    simp

