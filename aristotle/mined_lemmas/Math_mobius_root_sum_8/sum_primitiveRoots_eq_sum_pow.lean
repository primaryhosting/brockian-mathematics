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
