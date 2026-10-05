/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math

/-- The primitive 5-th roots of unity in `ℂ` are exactly the powers `ζ, ζ², ζ³, ζ⁴`
of `ζ = exp(2πi/5)`. -/

lemma primitiveRoots_five_eq_image :
    primitiveRoots 5 ℂ =
      Finset.image (fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / 5) ^ i) {1, 2, 3, 4} := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    mem_primitiveRoots (show 0 < 5 by norm_num)]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ?_, rfl⟩
    interval_cases i
    · exfalso
      simp only [pow_zero] at hx
      have := hx.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)
      omega
    · tauto
    · tauto
    · tauto
    · tauto
  · rintro ⟨i, hi, rfl⟩
    refine hz.pow_of_coprime i ?_
    rcases hi with h | h | h | h <;> subst h <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ(5) = -1`. -/
