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

namespace Math

open ArithmeticFunction Finset

/-- The Möbius function at `10` equals `1`. -/

lemma notMem_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 ∉ ({ζ ^ 3, ζ ^ 7, ζ ^ 9} : Finset ℂ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨pow_ne_pow h (by norm_num) (by norm_num) (by norm_num),
    pow_ne_pow h (by norm_num) (by norm_num) (by norm_num),
    pow_ne_pow h (by norm_num) (by norm_num) (by norm_num)⟩

