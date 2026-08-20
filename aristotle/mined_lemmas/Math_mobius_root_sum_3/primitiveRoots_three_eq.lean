import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Complex

namespace Math

/-- The set of primitive `3`-rd roots of unity in `ℂ` consists of `ζ` and `ζ ^ 2`, for any
primitive `3`-rd root of unity `ζ`. -/

lemma primitiveRoots_three_eq {ζ : ℂ} (h : IsPrimitiveRoot ζ 3) :
    primitiveRoots 3 ℂ = {ζ, ζ ^ 2} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), h.isPrimitiveRoot_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, hcop, rfl⟩
    interval_cases i
    · exact absurd hcop (by decide)
    · exact Or.inl (pow_one ζ)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, by norm_num, rfl⟩

/-- The sum of the primitive `3`-rd roots of unity in `ℂ` equals `μ 3 = -1`. -/
