/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- A primitive `8`-th root of unity satisfies `z ^ 4 = -1`. -/

theorem isPrimitiveRoot_neg_of_eight {z : ℂ} (h : IsPrimitiveRoot z 8) :
    IsPrimitiveRoot (-z) 8 := by
  have h5 : z ^ 5 = -z := by
    have h4 := primRoot8_pow_four h
    calc z ^ 5 = z ^ 4 * z := by ring
      _ = -z := by rw [h4]; ring
  have := h.pow_of_coprime 5 (by decide)
  rwa [h5] at this

/-- **Möbius root sum for `n = 8`.** The sum of the primitive `8`-th roots of unity in `ℂ`
equals `μ 8` (which is `0`, since `8` is not squarefree).

The proof uses the fixed-point-free involution `z ↦ -z` on the set of primitive `8`-th roots
of unity, which forces the sum to be its own negative. -/
